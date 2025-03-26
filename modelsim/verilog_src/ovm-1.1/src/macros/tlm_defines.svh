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

// The following macros: ovm_IF_imp_decl all users to create implemenation
// classes which a predefined tlm interface but add a suffix to the 
// implementation methods. This allows multiple interfaces of the same type
// to be implemented in the same scope.
//
// For example:
//
// `ovm_blocking_put_imp_decl(_1)
// `ovm_blocking_put_imp_decl(_2)
// class my_put_imp#(type T=int) extends ovm_component;
//    ovm_blocking_put_imp_1#(T) export1;
//    ovm_blocking_put_imp_2#(T) export2;
//    ...
//    function void put_1 (input T t);
//      //puts comming into export1
//      ...
//    endfunction
//    function void put_2(input T t);
//      //puts comming into export2
//      ...
//    endfunction
// endclass

// Note that the default, unsuffixed, implementations live in the file
// tlm/ovm_imps.sv.

`define ovm_blocking_put_imp_decl(SFX) \
class ovm_blocking_put_imp``SFX #( type T=int , type IMP=int ) \
  extends ovm_port_base #( tlm_if_base #(T,T) ); \
 \
  local IMP m_imp; \
  \
  function new( string name , IMP imp ); \
    super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
     \
    m_if = this; \
    m_imp = imp; \
    m_if_mask = `TLM_BLOCKING_PUT_MASK; \
    m_if_name = "tlm_blocking_put"; \
    assert( this.m_connector.add_if( m_if ) ); \
  endfunction \
 \
  `ovm_get_type_name_func(ovm_blocking_put_imp``SFX # (T, IMP)) \
  `BLOCKING_PUT_IMP_SFX(SFX,m_imp , T , t ) \
 \
endclass

`define ovm_nonblocking_put_imp_decl(SFX) \
class ovm_nonblocking_put_imp``SFX #( type T=int , type IMP=int ) \
  extends ovm_port_base #( tlm_if_base #(T,T) ); \
 \
  local IMP m_imp; \
  \
  function new( string name , IMP imp ); \
    super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
     \
    m_if = this; \
    m_imp = imp; \
    m_if_mask = `TLM_NONBLOCKING_PUT_MASK; \
    m_if_name = "tlm_nonblocking_put"; \
    assert( this.m_connector.add_if( m_if ) ); \
  endfunction \
 \
  `ovm_get_type_name_func(ovm_nonblocking_put_imp``SFX # (T, IMP)) \
  `NONBLOCKING_PUT_IMP_SFX( SFX,m_imp , T , t ) \
   \
endclass

`define ovm_put_imp_decl(SFX) \
class ovm_put_imp #( type T=int , type IMP=int ) \
  extends ovm_port_base #( tlm_if_base #(T,T) ); \
 \
  local IMP m_imp; \
  \
  function new( string name , IMP imp ); \
    super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
     \
    m_if = this; \
    m_imp = imp; \
    m_if_mask = `TLM_PUT_MASK; \
    m_if_name = "tlm_put"; \
    assert( this.m_connector.add_if( m_if ) ); \
endfunction \
 \
  `ovm_get_type_name_func(ovm_put_imp``SFX # (T, IMP)) \
  `BLOCKING_PUT_IMP_SFX(SFX,m_imp , T , t ) \
  `NONBLOCKING_PUT_IMP_SFX(SFX,m_imp , T , t ) \
   \
endclass

`define ovm_blocking_get_imp_decl(SFX) \
class ovm_blocking_get_imp``SFX #( type T=int , type IMP=int ) \
  extends ovm_port_base #( tlm_if_base #(T,T) ); \
 \
  local IMP m_imp; \
  \
  function new( string name , IMP imp ); \
    super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
     \
    m_if = this; \
    m_imp = imp; \
    m_if_mask = `TLM_BLOCKING_GET_MASK; \
    m_if_name = "tlm_blocking_get"; \
    assert( this.m_connector.add_if( m_if ) ); \
  endfunction \
 \
  `ovm_get_type_name_func(ovm_blocking_get_imp``SFX # (T, IMP)) \
  `BLOCKING_GET_IMP_SFX(SFX,m_imp , T , t ) \
   \
endclass

`define ovm_nonblocking_get_imp_decl(SFX) \
class ovm_nonblocking_get_imp``SFX #( type T=int , type IMP=int ) \
  extends ovm_port_base #( tlm_if_base #(T,T) ); \
 \
  local IMP m_imp; \
  \
  function new( string name , IMP imp ); \
    super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
     \
    m_if = this; \
    m_imp = imp; \
    m_if_mask = `TLM_NONBLOCKING_GET_MASK; \
    m_if_name = "tlm_nonblocking_get"; \
    assert( this.m_connector.add_if( m_if ) ); \
  endfunction \
 \
  `ovm_get_type_name_func(ovm_nonblocking_get_imp``SFX # (T, IMP)) \
  `NONBLOCKING_GET_IMP_SFX(SFX,m_imp , T , t ) \
   \
endclass

`define ovm_get_imp_decl(SFX) \
class ovm_get_imp``SFX #( type T=int , type IMP=int ) \
  extends ovm_port_base #( tlm_if_base #(T,T) ); \
 \
  local IMP m_imp; \
  \
  function new( string name , IMP imp ); \
    super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
     \
    m_if = this; \
    m_imp = imp; \
    m_if_mask = `TLM_GET_MASK; \
    m_if_name = "tlm_get"; \
    assert( this.m_connector.add_if( m_if ) ); \
  endfunction \
 \
  `ovm_get_type_name_func(ovm_get_imp``SFX # (T, IMP)) \
  `BLOCKING_GET_IMP_SFX(SFX,m_imp , T , t ) \
  `NONBLOCKING_GET_IMP_SFX(SFX,m_imp , T , t ) \
   \
endclass

`define ovm_blocking_peek_imp_decl(SFX) \
class ovm_blocking_peek_imp``SFX #( type T=int , type IMP=int ) \
  extends ovm_port_base #( tlm_if_base #(T,T) ); \
 \
  local IMP m_imp; \
  \
  function new( string name , IMP imp ); \
    super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
     \
    m_if = this; \
    m_imp = imp; \
    m_if_mask = `TLM_BLOCKING_PEEK_MASK; \
    m_if_name = "tlm_blocking_peek"; \
    assert( this.m_connector.add_if( m_if ) ); \
  endfunction \
 \
  `ovm_get_type_name_func(ovm_blocking_peek_imp``SFX # (T, IMP)) \
  `BLOCKING_PEEK_IMP_SFX(SFX,m_imp , T , t ) \
   \
endclass 

`define ovm_nonblocking_peek_imp_decl(SFX) \
class ovm_nonblocking_peek_imp``SFX #( type T=int , type IMP=int ) \
  extends ovm_port_base #( tlm_if_base #(T,T) ); \
 \
  local IMP m_imp; \
  \
  function new( string name , IMP imp ); \
    super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
     \
    m_if = this; \
    m_imp = imp; \
    m_if_mask = `TLM_NONBLOCKING_PEEK_MASK; \
    m_if_name = "tlm_nonblocking_peek"; \
    assert( this.m_connector.add_if( m_if ) ); \
  endfunction \
 \
  `ovm_get_type_name_func(ovm_nonblocking_peek_imp``SFX # (T, IMP)) \
  `NONBLOCKING_PEEK_IMP_SFX(SFX,m_imp , T , t ) \
   \
endclass

`define ovm_peek_imp_decl(SFX) \
class ovm_peek_imp``SFX #( type T=int , type IMP=int ) \
  extends ovm_port_base #( tlm_if_base #(T,T) ); \
 \
  local IMP m_imp; \
  \
  function new( string name , IMP imp ); \
    super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
     \
    m_if = this; \
    m_imp = imp; \
    m_if_mask = `TLM_PEEK_MASK; \
    m_if_name = "tlm_peek"; \
    assert( this.m_connector.add_if( m_if ) ); \
  endfunction \
 \
  `ovm_get_type_name_func(ovm_peek_imp``SFX # (T, IMP)) \
  `BLOCKING_PEEK_IMP_SFX(SFX,m_imp , T , t ) \
  `NONBLOCKING_PEEK_IMP_SFX(SFX,m_imp , T , t ) \
   \
endclass


`define ovm_blocking_get_peek_imp_decl(SFX) \
class ovm_blocking_get_peek_imp``SFX #( type T=int , type IMP=int ) \
  extends ovm_port_base #( tlm_if_base #(T,T) ); \
 \
  local IMP m_imp; \
  \
  function new( string name , IMP imp ); \
    super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
     \
    m_if = this; \
    m_imp = imp; \
    m_if_mask = `TLM_BLOCKING_GET_PEEK_MASK; \
    m_if_name = "tlm_blocking_get_peek"; \
    assert( this.m_connector.add_if( m_if ) ); \
  endfunction \
 \
  `ovm_get_type_name_func(ovm_blocking_get_peek_imp``SFX # (T, IMP)) \
  `BLOCKING_GET_IMP_SFX(SFX,m_imp , T , t ) \
  `BLOCKING_PEEK_IMP_SFX(SFX,m_imp , T , t ) \
   \
endclass

`define ovm_nonblocking_get_peek_imp_decl(SFX) \
class ovm_nonblocking_get_peek_imp``SFX #( type T=int , type IMP=int ) \
  extends ovm_port_base #( tlm_if_base #(T,T) ); \
 \
  local IMP m_imp; \
  \
  function new( string name , IMP imp ); \
    super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
     \
    m_if = this; \
    m_imp = imp; \
    m_if_mask = `TLM_NONBLOCKING_GET_PEEK_MASK; \
    m_if_name = "tlm_nonblocking_get_peek"; \
    assert( this.m_connector.add_if( m_if ) ); \
  endfunction \
 \
  `ovm_get_type_name_func(ovm_nonblocking_get_peek_imp``SFX # (T, IMP)) \
  `NONBLOCKING_GET_IMP_SFX(SFX,m_imp , T , t ) \
  `NONBLOCKING_PEEK_IMP_SFX(SFX,m_imp , T , t ) \
   \
endclass

`define ovm_get_peek_imp_decl(SFX) \
class ovm_get_peek_imp``SFX #( type T=int , type IMP=int ) \
  extends ovm_port_base #( tlm_if_base #(T,T) ); \
 \
  local IMP m_imp; \
  \
  function new( string name , IMP imp ); \
    super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
     \
    m_if = this; \
    m_imp = imp; \
    m_if_mask = `TLM_GET_PEEK_MASK; \
    m_if_name = "tlm_get_peek"; \
    assert( this.m_connector.add_if( m_if ) ); \
  endfunction \
 \
  `ovm_get_type_name_func(ovm_get_peek_imp``SFX # (T, IMP)) \
  `BLOCKING_GET_IMP_SFX(SFX,m_imp , T , t ) \
  `NONBLOCKING_GET_IMP_SFX(SFX,m_imp , T , t ) \
     \
   `BLOCKING_PEEK_IMP_SFX(SFX,m_imp , T , t ) \
  `NONBLOCKING_PEEK_IMP_SFX(SFX,m_imp , T , t ) \
   \
endclass

`define ovm_blocking_master_imp_decl(SFX) \
class ovm_blocking_master_imp``SFX #( type REQ=int , type RSP=int , \
				 type IMP=int , \
				 type REQ_IMP=IMP , \
				 type RSP_IMP=IMP ) \
  extends ovm_port_base #( tlm_if_base #(REQ, RSP) ); \
 \
  local REQ_IMP m_req_imp; \
  local RSP_IMP m_rsp_imp; \
 \
 \
   function new( string name , IMP imp , \
		 REQ_IMP req_imp = imp , RSP_IMP rsp_imp = imp ); \
     super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
      \
     m_if = this; \
     m_req_imp = req_imp; \
     m_rsp_imp = rsp_imp; \
    m_if_mask = `TLM_BLOCKING_MASTER_MASK; \
    m_if_name = "tlm_blocking_master"; \
    assert( this.m_connector.add_if( m_if ) ); \
  endfunction  \
 \
  `ovm_get_type_name_func(ovm_blocking_master_imp``SFX # (T, IMP)) \
  `BLOCKING_PUT_IMP_SFX(SFX,m_req_imp , REQ , t ) // req \
 \
  `BLOCKING_GET_IMP_SFX(SFX,m_rsp_imp , RSP , t ) // rsp \
  `BLOCKING_PEEK_IMP_SFX(SFX,m_rsp_imp , RSP , t ) // rsp \
   \
endclass

`define ovm_nonblocking_master_imp_decl(SFX) \
class ovm_nonblocking_master_imp #( type REQ=int , type RSP=int , \
				    type IMP=int , \
				    type REQ_IMP=IMP , \
				    type RSP_IMP=IMP ) \
   \
  extends ovm_port_base #( tlm_if_base #(REQ, RSP) ); \
 \
  local REQ_IMP m_req_imp; \
  local RSP_IMP m_rsp_imp; \
 \
   function new( string name , IMP imp , \
		 REQ_IMP req_imp = imp , RSP_IMP rsp_imp = imp ); \
     super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
      \
     m_if = this; \
     m_req_imp = req_imp; \
     m_rsp_imp = rsp_imp; \
      \
    m_if_mask = `TLM_NONBLOCKING_MASTER_MASK; \
    m_if_name = "tlm_nonblocking_master"; \
    assert( this.m_connector.add_if( m_if ) ); \
  endfunction  \
 \
  `ovm_get_type_name_func(ovm_nonblocking_master_imp``SFX # (T, IMP)) \
  `NONBLOCKING_PUT_IMP_SFX(SFX,m_req_imp , REQ , t ) // req \
 \
  `NONBLOCKING_GET_IMP_SFX(SFX,m_rsp_imp , RSP , t ) // rsp \
  `NONBLOCKING_PEEK_IMP_SFX(SFX,m_rsp_imp , RSP , t ) // rsp \
   \
endclass

`define ovm_master_imp_decl(SFX) \
class ovm_master_imp``SFX #( type REQ=int , type RSP=int , \
			type IMP=int , \
			type REQ_IMP=IMP , type RSP_IMP=IMP ) \
  extends ovm_port_base #( tlm_if_base #(REQ, RSP) ); \
 \
  local REQ_IMP m_req_imp; \
  local RSP_IMP m_rsp_imp; \
 \
   function new( string name , IMP imp , \
		 REQ_IMP req_imp = imp , RSP_IMP rsp_imp = imp ); \
     super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
      \
     m_if = this; \
     m_req_imp = req_imp; \
     m_rsp_imp = rsp_imp; \
    m_if_mask = `TLM_MASTER_MASK; \
    m_if_name = "tlm_master"; \
    assert( this.m_connector.add_if( m_if ) ); \
  endfunction  \
 \
  `ovm_get_type_name_func(ovm_master_imp``SFX # (T, IMP)) \
  `BLOCKING_PUT_IMP_SFX(SFX,m_req_imp , REQ , t ) // req \
  `NONBLOCKING_PUT_IMP_SFX(SFX,m_req_imp , REQ , t ) // req \
 \
  `BLOCKING_GET_IMP_SFX(SFX,m_rsp_imp , RSP , t ) // rsp \
  `BLOCKING_PEEK_IMP_SFX(SFX,m_rsp_imp , RSP , t ) // rsp \
  `NONBLOCKING_GET_IMP_SFX(SFX,m_rsp_imp , RSP , t ) // rsp \
  `NONBLOCKING_PEEK_IMP_SFX(SFX,m_rsp_imp , RSP , t ) // rsp \
    \
endclass

`define ovm_blocking_slave_imp_decl(SFX) \
class ovm_blocking_slave_imp``SFX #( type REQ=int , type RSP=int , \
				type IMP=int , \
				type REQ_IMP=IMP , \
				type RSP_IMP=IMP ) \
   \
  extends ovm_port_base #( tlm_if_base #(RSP, REQ) ); \
 \
  local REQ_IMP m_req_imp; \
  local RSP_IMP m_rsp_imp; \
 \
   function new( string name , IMP imp , \
		 REQ_IMP req_imp = imp , RSP_IMP rsp_imp = imp ); \
     super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
      \
     m_if = this; \
     m_req_imp = req_imp; \
     m_rsp_imp = rsp_imp; \
    m_if_mask = `TLM_BLOCKING_SLAVE_MASK; \
    m_if_name = "tlm_blocking_slave"; \
      \
    assert( this.m_connector.add_if( m_if ) ); \
  endfunction  \
 \
  `ovm_get_type_name_func(ovm_blocking_slave_imp``SFX # (T, IMP)) \
  `BLOCKING_PUT_IMP_SFX(SFX,m_rsp_imp , RSP , t ) // rsp \
 \
  `BLOCKING_GET_IMP_SFX(SFX,m_req_imp , REQ , t ) // req \
  `BLOCKING_PEEK_IMP_SFX(SFX,m_req_imp , REQ , t ) // req \
   \
endclass

`define ovm_nonblocking_slave_imp_decl(SFX) \
class ovm_nonblocking_slave_imp``SFX #( type REQ=int , type RSP=int , \
				   type IMP=int , \
				   type REQ_IMP=IMP , \
				   type RSP_IMP=IMP ) \
   \
  extends ovm_port_base #( tlm_if_base #(RSP, REQ) ); \
 \
  local REQ_IMP m_req_imp; \
  local RSP_IMP m_rsp_imp; \
 \
   function new( string name , IMP imp , \
		 REQ_IMP req_imp = imp , RSP_IMP rsp_imp = imp ); \
     super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
      \
     m_if = this; \
     m_req_imp = req_imp; \
     m_rsp_imp = rsp_imp; \
    m_if_mask = `TLM_NONBLOCKING_SLAVE_MASK; \
    m_if_name = "tlm_nonblocking_slave"; \
      \
    assert( this.m_connector.add_if( m_if ) ); \
  endfunction  \
 \
  `ovm_get_type_name_func(ovm_nonblocking_slave_imp``SFX # (T, IMP)) \
  `NONBLOCKING_PUT_IMP_SFX(SFX,m_rsp_imp , RSP , t ) // rsp \
 \
  `NONBLOCKING_GET_IMP_SFX(SFX,m_req_imp , REQ , t ) // req \
  `NONBLOCKING_PEEK_IMP_SFX(SFX,m_req_imp , REQ , t ) // req \
   \
endclass

`define ovm_slave_imp_decl(SFX) \
class ovm_slave_imp``SFX #( type REQ=int , type RSP=int , \
		       type IMP=int , \
		       type REQ_IMP=IMP , type RSP_IMP=IMP ) \
  extends ovm_port_base #( tlm_if_base #(RSP, REQ) ); \
 \
  local REQ_IMP m_req_imp; \
  local RSP_IMP m_rsp_imp; \
 \
   function new( string name , IMP imp , \
		 REQ_IMP req_imp = imp , RSP_IMP rsp_imp = imp ); \
     super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
      \
     m_if = this; \
     m_req_imp = req_imp; \
     m_rsp_imp = rsp_imp; \
    m_if_mask = `TLM_SLAVE_MASK; \
    m_if_name = "tlm_slave"; \
      \
    assert( this.m_connector.add_if( m_if ) ); \
  endfunction  \
 \
  `ovm_get_type_name_func(ovm_slave_imp``SFX # (T, IMP)) \
  `BLOCKING_PUT_IMP_SFX(SFX,m_rsp_imp , RSP , t ) // rsp \
  `NONBLOCKING_PUT_IMP_SFX(SFX,m_rsp_imp , RSP , t ) // rsp \
 \
  `BLOCKING_GET_IMP_SFX(SFX,m_req_imp , REQ , t ) // req \
  `BLOCKING_PEEK_IMP_SFX(SFX,m_req_imp , REQ , t ) // req \
  `NONBLOCKING_GET_IMP_SFX(SFX,m_req_imp , REQ , t ) // req \
  `NONBLOCKING_PEEK_IMP_SFX(SFX,m_req_imp , REQ , t ) // req \
    \
endclass

`define ovm_blocking_transport_imp_decl(SFX) \
class ovm_blocking_transport_imp``SFX #( type REQ=int , \
                                    type RSP=int , type IMP=int ) \
  extends ovm_port_base #( tlm_if_base #(REQ, RSP) ); \
 \
  local IMP m_imp; \
  \
  function new( string name , IMP imp ); \
    super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
     \
    m_if = this; \
    m_imp = imp; \
    m_if_mask = `TLM_BLOCKING_TRANSPORT_MASK; \
    m_if_name = "tlm_blocking_transport"; \
    assert( this.m_connector.add_if( m_if ) ); \
  endfunction \
 \
  `ovm_get_type_name_func(ovm_blocking_transport_imp``SFX # (T, IMP)) \
  `BLOCKING_TRANSPORT_IMP``SFX(SFX,m_imp, REQ, RSP, req, rsp) \
   \
endclass

`define ovm_non_blocking_transport_imp_decl(SFX) \
class ovm_nonblocking_transport_imp``SFX #( type REQ=int , \
                                       type RSP=int , type IMP=int ) \
  extends ovm_port_base #( tlm_if_base #(REQ, RSP) ); \
 \
  local IMP m_imp; \
  \
  function new( string name , IMP imp ); \
    super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
     \
    m_if = this; \
    m_imp = imp; \
    m_if_mask = `TLM_NONBLOCKING_TRANSPORT_MASK; \
    m_if_name = "tlm_nonblocking_transport"; \
    assert( this.m_connector.add_if( m_if ) ); \
  endfunction \
 \
  `ovm_get_type_name_func(ovm_nonblocking_transport_imp``SFX # (T, IMP)) \
  `NONBLOCKING_TRANSPORT_IMP_SFX(SFX,m_imp, REQ, RSP, req, rsp) \
   \
endclass

`define ovm_transport_imp_decl(SFX) \
class ovm_transport_imp`SFX #( type REQ=int , \
                           type RSP=int , type IMP=int ) \
  extends ovm_port_base #( tlm_if_base #(REQ, RSP) ); \
 \
  local IMP m_imp; \
  \
  function new( string name , IMP imp ); \
    super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
     \
    m_if = this; \
    m_imp = imp; \
    m_if_mask = `TLM_TRANSPORT_MASK; \
    m_if_name = "tlm_transport"; \
    assert( this.m_connector.add_if( m_if ) ); \
  endfunction \
 \
  `ovm_get_type_name_func(ovm_transport_imp``SFX # (T, IMP)) \
  `BLOCKING_TRANSPORT_IMP_SFX(SFX,m_imp, REQ, RSP, req, rsp) \
  `NONBLOCKING_TRANSPORT_IMP_SFX(SFX,m_imp, REQ, RSP, req, rsp) \
   \
endclass

`define ovm_analysis_imp_decl(SFX) \
class ovm_analysis_imp``SFX #( type T=int , type IMP=int ) \
  extends ovm_port_base #( tlm_if_base #(T,T) ); \
 \
  local IMP m_imp; \
  \
  function new( string name , IMP imp ); \
    super.new( name , imp , OVM_IMPLEMENTATION , 1 , 1 ); \
     \
    m_if = this; \
    m_imp = imp; \
    m_if_mask = `TLM_ANALYSIS_MASK; \
    m_if_name = "tlm_analysis"; \
    assert( this.m_connector.add_if( m_if ) ); \
  endfunction \
 \
  `ovm_get_type_name_func(ovm_analysis_imp``SFX # (T, IMP)) \
  function void write( input T t ); \
    m_imp.write``SFX( t ); \
  endfunction \
   \
endclass


//
// These imps are used in ovm_*_port, ovm_*_export and ovm_*_imp, using suffixes
//

`define BLOCKING_PUT_IMP_SFX(SFX,imp , TYPE , arg ) \
  task put( input TYPE arg ); imp.put``SFX( arg ); endtask

`define BLOCKING_GET_IMP_SFX(SFX,imp , TYPE , arg ) \
  task get( output TYPE arg ); imp.get``SFX( arg ); endtask

`define BLOCKING_PEEK_IMP_SFX(SFX,imp , TYPE , arg ) \
  task peek( output TYPE arg );imp.peek``SFX( arg ); endtask

`define NONBLOCKING_PUT_IMP_SFX(SFX,imp , TYPE , arg ) \
  function bit try_put( input TYPE arg ); \
    if( !imp.try_put``SFX( arg ) ) return 0; \
    return 1; \
  endfunction \
  function bit can_put(); return imp.can_put``SFX(); endfunction

`define NONBLOCKING_GET_IMP_SFX(SFX,imp , TYPE , arg ) \
  function bit try_get( output TYPE arg ); \
    if( !imp.try_get``SFX( arg ) ) return 0; \
    return 1; \
  endfunction \
  function bit can_get(); return imp.can_get``SFX(); endfunction

`define NONBLOCKING_PEEK_IMP_SFX(SFX,imp , TYPE , arg ) \
  function bit try_peek( output TYPE arg ); \
    if( !imp.try_peek``SFX( arg ) ) return 0; \
    return 1; \
  endfunction \
  function bit can_peek(); return imp.can_peek``SFX(); endfunction

`define BLOCKING_TRANSPORT_IMP_SFX(SFX,imp, REQ, RSP, req_arg, rsp_arg) \
  task transport( input REQ req_arg, output RSP rsp_arg); \
    imp.transport``SFX(req_arg, rsp_arg); \
  endtask

`define NONBLOCKING_TRANSPORT_IMP_SFX(SFX,imp, REQ, RSP, req_arg, rsp_arg) \
  function void nb_transport( input REQ req_arg, output RSP rsp_arg); \
    if(imp) imp.nb_transport``SFX(req_arg, rsp_arg); \
  endfunction

