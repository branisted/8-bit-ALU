// $Id: //dvt/mti/rel/6.5b/src/misc/ovm_src/ovm-1.1/src/methodology/ovm_scoreboard.svh#1 $
//----------------------------------------------------------------------
//   Copyright 2007-2009 Mentor Graphics Corporation
//   Copyright 2007-2009 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
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

`ifndef OVM_SCOREBOARD_SVH
`define OVM_SCOREBOARD_SVH

//------------------------------------------------------------------------------
//
// CLASS: ovm_scoreboard
//
// declaration
//------------------------------------------------------------------------------

virtual class ovm_scoreboard extends ovm_threaded_component;

  // Constructor
  extern function new (input string name, input ovm_component parent);

  task run; begin end endtask
endclass : ovm_scoreboard

`endif // OVM_SCOREBOARD_SVH

