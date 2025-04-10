// $Id: //dvt/mti/rel/6.5b/src/misc/avm_src/deprecated/avm_stimulus.svh#1 $
//----------------------------------------------------------------------
//   Copyright 2005-2009 Mentor Graphics Corporation
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------


// A general purpose unidirectional random stimulus class.
//
// If you want to do stuff before or after the run method,
// extend this class, define your own run, and call
// super.run( . ). This will be the case, for example when
// you need a non random initialisation sequence before you
// do some constraint random testing.
//

// The avm_stimulus class generates streams of trans_type
// transactions. These streams may be generated by the
// randomize method of trans_type, or the randomize method
// of one of its subclasses.  The stream may go
// indefinitely, until terminated by a call to
// stop_stimulus_generation, or we may specify the maximum
// number of transactions to be generated.
//
// By using inheritance, we can add directed initialization
// or tidy up sequences to the random stimulus generation.

// begin codeblock avm_stimulus_header
class avm_stimulus #( type trans_type = avm_transaction )
  extends avm_named_component;

  // blocking_put_port is the port used to send the
  // generated stimulus to the rest of the testbench

  tlm_blocking_put_if #( trans_type ) blocking_put_port;
  
// end codeblock avm_stimulus_header caption path
  local bit m_stop = 0;

  // Constructor
  //
  // We must always specify a local name. We should not
  // specify a parent if this component is instantiated
  // inside the environment class. We should specify a
  // parent is this component is instantiated inside another
  // named component.
  //
  // The constructor also displays the string obtained from
  // get_randstate during construction.  set_randstate can
  // be then used to regenerate precisely the same sequence
  // of transactions for debugging purposes.

  function new( string name ,
                avm_named_component parent = null );

    string seed_str;

    super.new( name , parent );
    m_stop = 0;

    avm_report_warning( s_deprecated_3_0 , "avm_stimulus is deprecated in AVM 3.0 and later, since it uses AVM 2.0 style ports" );
    avm_report_message( s_deprecated_3_0 , "Please use avm_random_stimulus, which has AVM 3.0 style ports, instead" );
    
    $sformat( seed_str  , "rand state is %d" , get_randstate() );

    avm_report_message("avm_stimulus" , seed_str );
  endfunction

  // Generate stimulus is the main user visible method.
  //
  // If t is not specified, we will use the randomize method
  // in trans_type to generate transactions.  If t is
  // specified, we will use the randomize method in t to
  // generate transactions - so t must be a subclass of
  // trans_type.
  //
  // max_count is the maximum number of transactions to be
  // generated. A value of zero indicates no maximum - in
  // this case, generate_stimulus will go on indefinitely
  // unless stopped by some other process
  //
  // The transactions are cloned before they are sent out 
  // over the blocking_put_port

  virtual task generate_stimulus( trans_type t = null , 
                                  input int max_count = 0 );

    trans_type temp;
    
    if( t == null ) t = new;
    
    for( int i = 0; 
      (max_count == 0 || i < max_count) && !m_stop; 
       i++ ) begin

       assert( t.randomize() );
      
       $cast( temp , t.clone() );
       avm_report_message("stimulus generation" , 
                           temp.convert2string() );
       blocking_put_port.put( temp );
    end
  endtask
  
  // This method stops the generation of stimulus.
  //
  // If a subclass of this method has forked additional
  // processes, those processes will also need to be
  // stopped in an overridden version of this method
  
  virtual function void stop_stimulus_generation;
    m_stop = 1;
  endfunction
  
endclass : avm_stimulus
