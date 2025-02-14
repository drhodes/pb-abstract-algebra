

Authoring has n distinct phases.
- Editing the lecture material which involves writing auxml
  - For authors, most content is text and media elements.
  - Some content might need automation, such as automatic section
    numbering, theorem numbering, definition numbering, etc.
  - auxml has weak macros, they do not support conditional expressions
    and other features found in general programming languages because
    these structure add unnecessary complexity.  The macros of auxml
    are simple, they take arguments, expand and that's just about it.
    
- phase 2: running auxml, 
  Macro are expanded, auxml source is fully expanded into html.


- phase 3: <patchup/> phase (not strictly necessary)

  After the macros are expanded, any patchup elements are passed to
  their associated patchup functions which are written in python.
  
  This is easy to understand, there is no magic. Once the macros are
  expanded into an html document, any patchup elements (which looks
  like this):
    
  <patchup func="replace_with_div"/> 
  
  are passed to user defined python functions that look like this:
  
  ```python
  
  def my_patchup_func(patchup_element, tree):
      ''' 
      replace the element with a div
      '''
      
      # this is easy, just change the tag of the patchup_element.
      element.tag = "div"
      element.text = "Some text that goes in the div"
  ```

  This function lives in an arbitary python script.  As noted this
  phase is not strictly necessary. You could very well do the same
  thing by running your own scripts over the expanded html after
  running auxml. However, using the patchup facility offers a chance
  to edit the html tree before <outfile> elements are written out to
  disk.


