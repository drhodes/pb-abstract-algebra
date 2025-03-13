import copy
import os
from lxml import etree
import re

# patchup file.

# def include_namespace(tree, el):
#     el.tag = "div"
#     filename = el.get("file")
#     ns = el.get("namespace")

#     print(ns)
#     print(filename)
#     if not os.path.isfile(filename):
#         raise Exception(f"Could not find lean source {{filename}}")

#     text = open(filename).read()

#     pattern = rf'(namespace\s+{re.escape(ns)}.*?end\s+{re.escape(ns)})'    
#     match = re.search(pattern, text, re.DOTALL)
    
#     if match:
#         text = match.group(1).strip()
#         cleaned_text = re.sub(r'\n*\s*section solution.*?end solution', '\n', text, flags=re.DOTALL)
#         cleaned_text.strip()
#         el.text = re.sub(r'\n{3,}', '\n\n', cleaned_text)
#     else:
#         el.text = f"Could not find namespace {ns}"
#         print("No match found")
    
#     return tree

def get_line_number(text, start_pos):
    """
    Returns the line number of the start position in the text.
    """
    lines_before = text[:start_pos].splitlines()  # All lines before the match
    return len(lines_before) + 1  # Line numbers are 1-based

def include_namespace(tree, el):
    el.tag = "div"
    filename = el.get("file")
    ns = el.get("namespace")

    print(ns)
    print(filename)
    
    if not os.path.isfile(filename):
        raise Exception(f"Could not find lean source {filename}")

    with open(filename, 'r') as f:
        text = f.read()

    pattern = rf'(namespace\s+{re.escape(ns)}.*?end\s+{re.escape(ns)})'    
    match = re.search(pattern, text, re.DOTALL)
    
    if match:
        # Get the start of the match and calculate the line number using the helper function
        start_pos = match.start()
        line_number = get_line_number(text, start_pos)
        el.set("line-number", str(line_number))
        print(f"Namespace {ns} starts at line {line_number}")
        
        # Clean up the solution section and strip the result
        text = match.group(1).strip()
        cleaned_text = re.sub(r'\n*\s*section solution.*?end solution', '\n', text, flags=re.DOTALL).strip()
        el.text = re.sub(r'\n{3,}', '\n\n', cleaned_text)
    else:
        el.text = f"Could not find namespace {ns}"
        print("No match found")
    
    return tree





def include_solution(tree, el):
    el.tag = "pre"
    filename = el.get("file")
    ns = el.get("namespace")

    print(ns)
    print(filename)
    if not os.path.isfile(filename):
        raise Exception(f"Could not find lean source {filename}")

    text = open(filename).read()

    # Extract the namespace content
    ns_pattern = rf'namespace\s+{re.escape(ns)}(.*?)end\s+{re.escape(ns)}'
    ns_match = re.search(ns_pattern, text, re.DOTALL)
    
    if ns_match:
        ns_content = ns_match.group(1).strip()
        
        # Extract only the solution section
        solution_pattern = r'section\s+solution(.*?)end\s+solution'
        solution_match = re.search(solution_pattern, ns_content, re.DOTALL)
        
        if solution_match:
            el.text = solution_match.group(1).strip()
        else:
            el.text = "No solution section found"
    else:
        el.text = "No matching namespace found"
 
    return tree


def mathlib_source(tree, el):
    el.tag = "div"
    toolchain="/mnt/30bc0de0-c8b5-45f8-a015-d23ef2ec01d8/.elan/toolchains/leanprover--lean4---v4.15.0-rc1"
    path = f'{toolchain}/{el.get("file")}'
    idx1 = int(el.get("from"))
    idx2 = int(el.get("to"))

    txt = open(path).readlines()[idx1:idx2]
    el.text = ''.join(txt)

def mylib_source(tree, el):
    el.tag = "div"
    path = f'{el.get("file")}'
    idx1 = int(el.get("from"))
    idx2 = int(el.get("to"))

    txt = open(path).readlines()[idx1:idx2]
    el.text = ''.join(txt)
    
def build_the_sidebar(tree, curpage):
    
    lectures = tree.xpath('//*[@class="lecture"]')
    sb = etree.Element("ul")
    for lec in lectures:
        #      <li>
        #          <details id="lecture-n" open>
        #              <summary>Lecture-N Title</summary>
        #              ... here.
        #          </details>
        #      </li>
        
        node_lec_li = etree.Element("li")
        node_lec_details = etree.Element("details")
        node_lec_li.append(node_lec_details)
        node_lec_summary = etree.Element("summary")
        node_lec_details.append(node_lec_summary)
        
        lec_title = lec.get("title")
        node_lec_link = etree.Element("a")
        node_lec_link.text = lec_title
        
        node_lec_summary.append(node_lec_link)
        node_lec_details.append(node_lec_summary)
        
        on_first_page = True
        node_page_ul = etree.Element("ul")        
        for page in lec.xpath('.//*[@class="page"]'):
            url = f"../{page.get('path')}.html"
            if on_first_page:
                node_lec_link.set("href", url)
                on_first_page = False
            node_page_li = etree.Element("li")
            pagelink = etree.Element("a", title=lec_title)
            pagelink.set("href" , url)
            node_page_ul.append(node_page_li)
            node_page_li.append(pagelink)
            pagelink.text = page.get("title")
            if page.get("path") == curpage.get("path"):
                node_page_li.set("class", "cur-page")
                node_lec_details.set("open", "true")
                
        node_lec_details.append(node_page_ul)
        sb.append(node_lec_li)
    return sb
        
def insert_sidebars(tree, el):
    el.tag = "div"
    
    for page in tree.xpath('//*[@class="page"]'):        
        lecture_menu = page.getparent().getparent().getparent().xpath('.//*[@class="lecture-menu"]')
        sb = build_the_sidebar(tree, page) #.get("title"))
        lecture_menu[0].append(sb)
    return tree

def contains_el(el1, el2):
    return el2 in el1.iterdescendants()

def nav_prev_next(tree, el):
    
    # get all page elements
    pages = tree.xpath('//*[@class="page"]')

    # which page are we on?
    this_page = [p for p in pages if contains_el(p, el)]
    if len(this_page) != 1:
        raise Exception("Hey! Could not find a page containing patchup element")
    else:
        this_page = this_page[0]

    # give the patchup element a new name just to make this code more
    # clear
    
    nav = el
    
    # the nav is a div at the bottom of the page.
    nav.tag = "div"
    
    # There are three cases dependsing on location of the page.    
    # 1) the first page has no previous page
    # 2) the last page has no next page
    # 3) middle pages have both a prev and next.

    def do_first_page(next_page):        
        prev_link = etree.Element("a", attrib={
            "class": "a-nav-inactive",
            "href": f"",
        })
        prev_link.text = "⇜ "
        nav.append(prev_link)
        
        next_link = etree.Element("a", attrib={
            "class": "a-nav",
            "href": f"../{next_page.get('path')}.html",
        })
        next_link.text = next_page.get('title') + " ⇝"
        nav.append(next_link)
        
    def do_middle_page(prev_page, next_page):
        prev_link = etree.Element("a", attrib={
            "class": "a-nav",
            "href": f"../{prev_page.get('path')}.html",
        })
        prev_link.text = "⇜ " + prev_page.get('title')
        nav.append(prev_link)
        
        next_link = etree.Element("a", attrib={
            "class": "a-nav",
            "href": f"../{next_page.get('path')}.html",
        })
        next_link.text = next_page.get('title') + " ⇝"
        nav.append(next_link)

        
    def do_last_page(prev_page):
        prev_link = etree.Element("a", attrib={
            "class": "a-nav",
            "href": f"../{prev_page.get('path')}.html",
        })
        prev_link.text = "⇜ " + prev_page.get('title')
        nav.append(prev_link)
        
        next_link = etree.Element("a", attrib={
            "class": "a-nav-inactive",
            "href": f"",
        })
        next_link.text = ""
        nav.append(next_link)
        

    FIRST, MIDDLE, LAST = "FIRST", "MIDDLE", "LAST" 
    num_pages = len(pages)
    idx = pages.index(this_page)
    position = None
    
    if idx == 0:
        position = FIRST
    elif idx == len(pages) - 1:
        position = LAST
    else:
        position = MIDDLE
    

    match num_pages:
        case 0: raise Exception("this should not be possible")
        case 1:
            # we do not need a nav if this section only has one page:
            pass
        case 2 :
            # this page could be first or last page.
            match position:
                case "FIRST": do_first_page(pages[1])
                case "LAST": do_last_page(pages[0])
                case "MIDDLE": raise Exception("this should not be possible")
        case _:
            # this page could be first or last page.
            match position:
                case "FIRST": do_first_page(pages[1])
                case "LAST": do_last_page(pages[-2])
                case "MIDDLE": do_middle_page(pages[idx-1], pages[idx+1])



def git_hash(tree, el):
    from git import Repo
    repo = Repo(search_parent_directories=True)        
    el.tag = "span"
    el.text = repo.head.object.hexsha
