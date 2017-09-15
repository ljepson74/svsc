library ieee;
use ieee.std_logic_1164.all;
use IEEE.std_logic_arith.all; 
use IEEE.std_logic_unsigned.all; 

entity foo is
end foo;

architecture arch of foo is
  signal foo1 : std_logic_vector(3 downto 0);

    signal foo2 : std_logic_vector(3 downto 0);
--  signal foo2 : std_logic_vector(3 downto 0):=(others=>'1');
-- The above line replacement of the one above it will get rid of this warning below
--ASSERT/WARNING (time 0 FS) from package ieee.STD_LOGIC_ARITH, this builtin function called  from process :$PROCESS_000 (architecture worklib.foo:arch)
--Built-in relational argument contains a ('U', 'X', 'W', 'Z', '-') in an operand.

  
  signal foo3 : std_logic;
begin
  process
  begin
    foo2 <= foo1(2 downto 0) & foo3;
    if (foo2 = "1111") then foo3 <= '0';

    end if;
    wait;
  end process;

  process
  begin
    foo1 <= "0000";
    foo3 <= '0';
    wait for 5 ns;
    foo1 <= "0000";
    wait for 10 ns;
    foo1 <= "1111";
    wait for 10 ns;
    foo1 <= "1010";
    wait;
  end process ;
end arch;
