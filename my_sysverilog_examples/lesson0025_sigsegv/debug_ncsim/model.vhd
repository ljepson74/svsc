library ieee;
use ieee.std_logic_1164.all;
--
-- Note entity name must match exactly name of sc_module class in
--  SystemC
--
entity model is
  port (
--
-- Note that port names must match exactly port names as they appear in
--  sc_module class in SystemC; they must also match in order, mode and type.
--
    inPort : in std_logic;
    outPort : out std_logic
  );
end;

architecture SystemC of model is
--
-- Note that the foreign attribute string value must be "SystemC".
--
  attribute foreign of SystemC : architecture is "SystemC";
begin
end;
