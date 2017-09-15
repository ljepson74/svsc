entity top is end;

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_textio.all;
use STD.textio.all;

architecture a of top is
  signal inPort : std_logic;
  signal outPort : std_logic;
begin
  inPort <= 'Z',
            'X' after 10 ns,
            '0' after 20 ns,
            '1' after 30 ns;

  -- Instantiate the VHDL shell file for SystemC
  test : entity work.model port map (inPort, outPort);

  process (outPort)
    variable vline: line;
  begin
    write(vline, now);
    write(vline, string'("  inPort = "));
    write(vline, inPort);
    write(vline, string'(", outPort = "));
    write(vline, outPort);
    writeline(OUTPUT, vline);
  end process;

end;
