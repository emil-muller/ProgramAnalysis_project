import graphviz

"""
    The purpose of this file is to contain all functionality 
    to construct and render a sequence diagram
    pip install git+https://github.com/SamuelMarks/python-plantuml#egg=plantuml
"""

if __name__ == "__main__":
    dot = graphviz.Digraph()
    dot.node("A")
    dot.node("B")
    dot.edge("A","B")
    dot.render("dependency_graph.gv")