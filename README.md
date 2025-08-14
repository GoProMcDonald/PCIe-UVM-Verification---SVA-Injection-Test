# PCIe UVM Verification - SVA Injection Test

## Overview
This project demonstrates **SystemVerilog Assertions (SVA)** applied in a PCIe UVM verification environment.  
We intentionally inject protocol violations to verify that the assertions correctly detect illegal signal behaviors during simulation.

The DUT is a simplified PCIe transaction handler. The UVM testbench includes:
- **PCIe interface** (`pcie_if.sv`) with assertions embedded
- **UVM environment** with driver, monitor, scoreboard, and sequence
- **SVA injection mechanism** to force protocol violations

## Key Features
- **Assertion-based Verification (ABV)** integrated into the interface
- Automatic **protocol violation detection**
- UVM log messages and waveform dump for debugging
- Functional coverage and scoreboard checks

## File Structure

.
├── pcie_pkg.sv # UVM package: sequence item, scoreboard, enums, macros
├── pcie_if.sv # PCIe interface with assertions
├── design.sv # DUT logic
├── tb_top.sv # UVM testbench top module
├── pcie_driver.sv # UVM driver with SVA injection task
├── pcie_monitor.sv # UVM monitor capturing transactions
├── pcie_scoreboard.sv # Matches MRd/CPLD transactions
└── test.sv # UVM test class

<img width="904" height="694" alt="image" src="https://github.com/user-attachments/assets/de465bc7-4a1a-480d-babc-f99a9a01a553" />


## How It Works
1. **Normal Transaction Flow**:
   - Sequence sends valid PCIe transactions (MRd, MWr)
   - Driver drives `req_valid`/`req_ready` handshake
   - Monitor captures DUT responses
   - Scoreboard compares expected vs actual data

2. **SVA Injection**:
   - Driver includes a task to drop `req_valid` before `req_ready` is asserted
   - This violates the "valid must hold until ready" property

3. **Assertion Detection**:
   - `pcie_if.sv` contains:
     ```systemverilog
     property a_req_valid_hold;
       @(posedge clk) disable iff (!rst_n)
         req_valid && !req_ready |=> req_valid;
     endproperty
     assert property (a_req_valid_hold)
       else $fatal("SVA a_req_valid_hold violated");
     ```
   - When the violation occurs, simulation stops with a fatal message

## Example Simulation Log


UVM_INFO pcie_pkg.sv(189) @ 30000: uvm_test_top.env.agt.drv [pcie_driver] SVA inject: drop valid during wait @30000
UVM_INFO pcie_pkg.sv(270) @ 105000: uvm_test_top.env.agt.mon [MON] CAP MWr addr=0x10 tag=0 data=0xa5a50001
SVA a_req_valid_hold violated @125000
Fatal: "design.sv", 49: tb_top.vif.a_req_valid_hold: asserted failed at 125000 ps


## Waveform Analysis
At **125000 ps**:
- `req_valid` drops from 1 → 0
- `req_ready` is still 0
- Assertion `a_req_valid_hold` fires

## Running the Test on EDA Playground
1. Open EDA Playground and select:
   - **Language:** SystemVerilog
   - **Library:** Synopsys VCS 2023.03-SP2
2. Set compile options:
-timescale=1ns/1ns +vcs+flush+all +warn=all -sverilog
3. Upload all source files and run:
run_test("pcie_base_test");

## Key Takeaways
- **SVA is effective for protocol rule checking** and works seamlessly with UVM
- Injecting violations helps confirm that the assertions are functional
- Assertions in interfaces can be reused across multiple testbenches

## Next Steps
- Add more properties to check address stability, length matching, and tag rules
- Integrate assertion coverage into overall functional coverage report
- Expand sequences for more PCIe TLP types

---
**Author:** Yida Wang  
**Date:** Aug 14, 2025  


![Uploading image.png…]()
