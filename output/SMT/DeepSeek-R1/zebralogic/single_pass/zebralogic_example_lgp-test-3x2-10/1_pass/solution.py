from z3 import *

def main():
    # Define sorts for names and heights
    NameSort, (Eric, Arnold, Peter) = EnumSort('Name', ['Eric', 'Arnold', 'Peter'])
    HeightSort, (very_short, short, average) = EnumSort('Height', ['very_short', 'short', 'average'])
    
    # Create variables for names and heights of each house
    n1 = Const('n1', NameSort)
    n2 = Const('n2', NameSort)
    n3 = Const('n3', NameSort)
    h1 = Const('h1', HeightSort)
    h2 = Const('h2', HeightSort)
    h3 = Const('h3', HeightSort)
    
    s = Solver()
    
    # All names are distinct
    s.add(Distinct(n1, n2, n3))
    # All heights are distinct
    s.add(Distinct(h1, h2, h3))
    
    # Clue 1: Eric is not in the first house
    s.add(n1 != Eric)
    # Clue 4: Arnold is not in the first house
    s.add(n1 != Arnold)
    
    # Clue 3: The person who is very short is Eric
    # This means for whichever house has height very_short, the name must be Eric
    s.add(Implies(h1 == very_short, n1 == Eric))
    s.add(Implies(h2 == very_short, n2 == Eric))
    s.add(Implies(h3 == very_short, n3 == Eric))
    
    # Clue 2: The person who is very short is to the left of the person who is short.
    # We define the indices of the houses with very_short and short heights.
    vs_index = If(h1 == very_short, 1, If(h2 == very_short, 2, 3))
    s_index = If(h1 == short, 1, If(h2 == short, 2, 3))
    s.add(vs_index < s_index)
    
    # Check if there is a solution
    if s.check() == sat:
        model = s.model()
        
        # Helper function to convert Z3 constants to string names
        def name_to_str(val):
            if val == Eric: return "Eric"
            if val == Arnold: return "Arnold"
            if val == Peter: return "Peter"
        
        def height_to_str(val):
            if val == very_short: return "very short"
            if val == short: return "short"
            if val == average: return "average"
        
        # Extract values for each house
        house1 = ["1", name_to_str(model[n1]), height_to_str(model[h1])]
        house2 = ["2", name_to_str(model[n2]), height_to_str(model[h2])]
        house3 = ["3", name_to_str(model[n3]), height_to_str(model[h3])]
        
        # Prepare the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": [house1, house2, house3]
            }
        }
        
        # Print the JSON
        import json
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()