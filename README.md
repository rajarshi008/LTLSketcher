
*LTLSketcher* is a tool to solve the LTL sketching problem, which asks to complete a given LTL sketch (i.e., a partial LTL formula) to be consistent with data.
The tool is entirely built in Python3 using the SAT solver Z3.


### Installation
To install *LTLSketcher*, we recommend using a python virtual environment.
Typically, one can install and using a virtual environment as follows:
```
virutalenv -p python3 venv
source venv/bin/activate
```
Now, one must install the required python packages as follows:
```
pip install -r requirements.txt
```
*LTLSketcher* is now ready to use.

### Running
One can run *LTLSketcher* by simply running `python3 main.py`.
By default, this will run *LTLSketcher* on `example.trace` with the LTL Sketch `G(?1)`.  

#### Parameters
There are a variety of arguments that one can use to run *LTLSketcher*, as listed below:

|Argument        |Meaning
|----------------|------------------------------
|-i <file_name>| For specifying the name of the input file (to be located inside the `Scarlet` folder), default is *example.trace*.
|-s <sketch> | For specifying the LTL sketch
|-suf | For enabling the Suffix heuristic
|-bmc | For enabling the BMC heuristic

#### Input sample format:
The input sample file consist of traces separated as positives and negatives, separated by `---`.
Each trace is a sequence of letter separated by `;`. Each letter represents the truth value of atomic propositions.
An example of a trace is `1,0,1;0,0,0` which consists of two letters each of which define the values of three propositions (which by default consider to be `p,q,r`). An example input file looks like the following:
```
0,0,0;0,1,1;1,0,0;0,0,1;0,1,0
1,1,0;1,0,1;1,0,0;1,1,1;1,0,1
1,1,0;0,1,1;1,1,1;1,0,0;1,0,1
---
1,0,0;1,0,0;0,1,0;1,1,0;1,1,1
1,0,0;1,0,0;0,1,0;1,1,0;1,0,0
0,0,1;1,0,0;1,1,0;1,1,1;1,0,0
```
The input file must use the extension `.trace`.

#### Input Sketch Format:
A sketch must a partial LTL formula in which the missing information is indicated using ?.
We use `?i` to denote Type-0 placeholders, `?ui` to denote Type-1 placholders and `?bi` to denote Type-2 placeholders, where `i` is a natural number for indexing the placeholders. 
Here are some examples of LTL sketches `G(!(?1))`, `?u1(!(p))`, `?b1(F(q),?b2(!(p),q))`.
In the first example, there is only one Type-0 placeholder.
In the second example, there is only one Type-1 placeholder.
In the third example, there are two Type-2 placeholders.



