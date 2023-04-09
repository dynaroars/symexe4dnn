# symexe4dnn

## How to run
navigate to ```./src``` directory, and run the following:
```
python se.py <input>
```
Currently, we have a couple hardcoded input under ```./example```.

## Examples
1.   
    ```
    python se.py ../example/toy/4x3_1.py
    ```
    This is a toy DNN example that has 4 inputs, 3hidden layers, and 4 neurons at each layer (12 ReLU neurons). SE is able to scale on these kind of small networks.
    
    <img src="./img/4x3.png" />
     <br/>
    
    
    <details>

    <summary>Running Symexe4DNN on this example</summary>

    ```
    $ python se.py ../example/toy/4x3_1.py

    =========SE started=========
    layer: 0
            inputs: ['i0', 'i1']
    layer: 1
            inputs: ['n00', 'n01', 'n02', 'n03']
    layer: 2
            inputs: ['n10', 'n11', 'n12', 'n13']
    layer: 3
            inputs: ['n20', 'n21', 'n22', 'n23']
    ============================
    DONE:
    2       inputs
    4       layers
    2       outputs
    time used: 
    0.007296120000319206 s
    symbolic states obtained
    And(n00 ==
        If(1*i0 + 1*i1 + 1/10 <= 0, 0, 1*i0 + 1*i1 + 1/10),
        n01 ==
        If(1/2*i0 + 1/2*i1 + 1/5 <= 0, 0, 1/2*i0 + 1/2*i1 + 1/5),
        n02 ==
        If(3/2*i0 + 0*i1 + 3/10 <= 0, 0, 3/2*i0 + 0*i1 + 3/10),
        n03 ==
        If(0*i0 + 3/2*i1 + 2/5 <= 0, 0, 0*i0 + 3/2*i1 + 2/5),
        n10 ==
        If(1/2*n00 + -1/2*n01 + 0*n02 + 1*n03 + 1 <= 0,
        0,
        1/2*n00 + -1/2*n01 + 0*n02 + 1*n03 + 1),
        n11 ==
        If(-1/2*n00 + 1/10*n01 + 2*n02 + -3*n03 + -2 <= 0,
        0,
        -1/2*n00 + 1/10*n01 + 2*n02 + -3*n03 + -2),
        n12 ==
        If(1/2*n00 + -1/5*n01 + 2/5*n02 + 1*n03 + 3 <= 0,
        0,
        1/2*n00 + -1/5*n01 + 2/5*n02 + 1*n03 + 3),
        n13 ==
        If(-1/2*n00 + 1/10*n01 + 6/5*n02 + -1/2*n03 + -4 <= 0,
        0,
        -1/2*n00 + 1/10*n01 + 6/5*n02 + -1/2*n03 + -4),
        n20 ==
        If(1/2*n10 + -1/5*n11 + 1/2*n12 + 1/2*n13 + -1 <= 0,
        0,
        1/2*n10 + -1/5*n11 + 1/2*n12 + 1/2*n13 + -1),
        n21 ==
        If(-1/2*n10 + 1/10*n11 + 11/10*n12 + -1*n13 + 1 <= 0,
        0,
        -1/2*n10 + 1/10*n11 + 11/10*n12 + -1*n13 + 1),
        n22 ==
        If(1/2*n10 + -1/5*n11 + -1/2*n12 + 1/5*n13 + 1 <= 0,
        0,
        1/2*n10 + -1/5*n11 + -1/2*n12 + 1/5*n13 + 1),
        n23 ==
        If(-1/2*n10 + 1/10*n11 + 11/10*n12 + 2*n13 + -1 <= 0,
        0,
        -1/2*n10 + 1/10*n11 + 11/10*n12 + 2*n13 + -1),
        o0 == 1/2*n20 + 1/2*n21 + -2/5*n22 + 1*n23 + 1,
        o1 == -1/5*n20 + -1/2*n21 + 11/10*n22 + 2*n23 + 1)

    =========SE finished=========
    ```
    </details>
2. 
    ```
    python se.py ../example/acasxu/acasxu_1.py
    ```
    This is a DNN taken from the ACASXU flight navigation benchmark. This network has 5 in/outputs and 6 hidden layers each with 50 ReLU neurons (300 ReLu neurons). We are able to generate the symbolic state of this network, but the symbolic state is too large for the solver(z3) to solve.

    <details>
    <summary>Sample in/output</summary>

    ```
    $ python se.py ../example/acasxu/acasxu_1.py
    =========SE started=========
    layer: 0
            inputs: ['i0', 'i1', 'i2', 'i3', 'i4']
    layer: 1
            inputs: ['n00', 'n01', 'n02', 'n03', 'n04', 'n05', 'n06', 'n07', 'n08', 'n09', 'n010', 'n011', 'n012', 'n013', 'n014', 'n015', 'n016', 'n017', 'n018', 'n019', 'n020', 'n021', 'n022', 'n023', 'n024', 'n025', 'n026', 'n027', 'n028', 'n029', 'n030', 'n031', 'n032', 'n033', 'n034', 'n035', 'n036', 'n037', 'n038', 'n039', 'n040', 'n041', 'n042', 'n043', 'n044', 'n045', 'n046', 'n047', 'n048', 'n049']
    layer: 2
            inputs: ['n10', 'n11', 'n12', 'n13', 'n14', 'n15', 'n16', 'n17', 'n18', 'n19', 'n110', 'n111', 'n112', 'n113', 'n114', 'n115', 'n116', 'n117', 'n118', 'n119', 'n120', 'n121', 'n122', 'n123', 'n124', 'n125', 'n126', 'n127', 'n128', 'n129', 'n130', 'n131', 'n132', 'n133', 'n134', 'n135', 'n136', 'n137', 'n138', 'n139', 'n140', 'n141', 'n142', 'n143', 'n144', 'n145', 'n146', 'n147', 'n148', 'n149']
    layer: 3
            inputs: ['n20', 'n21', 'n22', 'n23', 'n24', 'n25', 'n26', 'n27', 'n28', 'n29', 'n210', 'n211', 'n212', 'n213', 'n214', 'n215', 'n216', 'n217', 'n218', 'n219', 'n220', 'n221', 'n222', 'n223', 'n224', 'n225', 'n226', 'n227', 'n228', 'n229', 'n230', 'n231', 'n232', 'n233', 'n234', 'n235', 'n236', 'n237', 'n238', 'n239', 'n240', 'n241', 'n242', 'n243', 'n244', 'n245', 'n246', 'n247', 'n248', 'n249']
    layer: 4
            inputs: ['n30', 'n31', 'n32', 'n33', 'n34', 'n35', 'n36', 'n37', 'n38', 'n39', 'n310', 'n311', 'n312', 'n313', 'n314', 'n315', 'n316', 'n317', 'n318', 'n319', 'n320', 'n321', 'n322', 'n323', 'n324', 'n325', 'n326', 'n327', 'n328', 'n329', 'n330', 'n331', 'n332', 'n333', 'n334', 'n335', 'n336', 'n337', 'n338', 'n339', 'n340', 'n341', 'n342', 'n343', 'n344', 'n345', 'n346', 'n347', 'n348', 'n349']
    layer: 5
            inputs: ['n40', 'n41', 'n42', 'n43', 'n44', 'n45', 'n46', 'n47', 'n48', 'n49', 'n410', 'n411', 'n412', 'n413', 'n414', 'n415', 'n416', 'n417', 'n418', 'n419', 'n420', 'n421', 'n422', 'n423', 'n424', 'n425', 'n426', 'n427', 'n428', 'n429', 'n430', 'n431', 'n432', 'n433', 'n434', 'n435', 'n436', 'n437', 'n438', 'n439', 'n440', 'n441', 'n442', 'n443', 'n444', 'n445', 'n446', 'n447', 'n448', 'n449']
    layer: 6
            inputs: ['n50', 'n51', 'n52', 'n53', 'n54', 'n55', 'n56', 'n57', 'n58', 'n59', 'n510', 'n511', 'n512', 'n513', 'n514', 'n515', 'n516', 'n517', 'n518', 'n519', 'n520', 'n521', 'n522', 'n523', 'n524', 'n525', 'n526', 'n527', 'n528', 'n529', 'n530', 'n531', 'n532', 'n533', 'n534', 'n535', 'n536', 'n537', 'n538', 'n539', 'n540', 'n541', 'n542', 'n543', 'n544', 'n545', 'n546', 'n547', 'n548', 'n549']
    ============================
    DONE:
    5       inputs
    7       layers
    5       outputs
    time used: 
    0.7024715990010009 s
    symbolic states obtained
    (smt formula omitted)
    ...

    =========SE finished=========
    1. Generating random inputs and obtain outputs
    failed to solve
    2. Simulating concrete execution
    failed to solve
    =============     =============
    =============DONE:============
    
    ```
    </details>


## dependencies
- z3-solver

If you want to try the ACASXU example, you will need the following packages 
- onnx
- onnx2pytorch
- torch

A conda envs is provided: ```envs.yaml```
