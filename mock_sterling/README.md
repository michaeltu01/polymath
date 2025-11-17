

Prototype MCP workflow:
  - invoke `racket <filename> -O run_sterling serve -O sterling_port <port>
  - using something like this "mock Sterling", query Forge for an instance
  - ask the model to explain the instance 
    - presumably need to prompt _generally_ to help interpret the JSON format

  
up to $5 Claude is perfectly fine -- we'll get you reimbursed

Question for next time: 
--What happens with multiple runs
  --what happens if the model has multiple run ideas
  --what happens if you get multiple instances
--What happens if you give it a run name (multiple runs/one run)
--Note --> it will infer a lot from allow so keep an eye out for alloy stuff in return docs
--What happens if you ahve two entries in color
--try more complex runs like tik tak to
--what happens if you give it a temporal mode, will it automatically understand that sequence or will it need additional context
--For after monday but dont forget it --> understand what it does with the question "why am i getting thsi instance"

--Take a glance at: https://cs.brown.edu/~tbn/publications/nddk-fse17-amalgam.pdf
