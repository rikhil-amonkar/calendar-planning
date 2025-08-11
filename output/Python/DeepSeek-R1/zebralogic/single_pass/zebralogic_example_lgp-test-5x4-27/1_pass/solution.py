import json

def main():
    # Initialize lists for attributes (index 0 unused, houses 1-5)
    names = [None] * 6
    birthdays = [None] * 6
    cigars = [None] * 6
    drinks = [None] * 6

    # Sets of remaining values
    names_remaining = set(['Peter', 'Alice', 'Eric', 'Bob', 'Arnold'])
    birthdays_remaining = set(['april', 'feb', 'mar', 'jan', 'sept'])
    cigars_remaining = set(['pall mall', 'prince', 'dunhill', 'blends', 'blue master'])
    drinks_remaining = set(['water', 'coffee', 'tea', 'milk', 'root beer'])

    # Helper function to assign a value to an attribute of a house and remove it from the remaining set
    def assign_value(house, attr_list, value, remaining_set):
        if attr_list[house] is not None:
            if attr_list[house] != value:
                raise RuntimeError(f"Conflict at house {house}: trying to assign {value} but already {attr_list[house]}")
            return
        attr_list[house] = value
        if value in remaining_set:
            remaining_set.remove(value)

    # Apply clues step by step
    try:
        # Clue 13: Eric is in the third house.
        assign_value(3, names, 'Eric', names_remaining)
        
        # Clue 1: The root beer lover is Eric.
        assign_value(3, drinks, 'root beer', drinks_remaining)
        
        # Clue 2: Pall Mall cigar in third house.
        assign_value(3, cigars, 'pall mall', cigars_remaining)
        
        # Clue 8: February birthday in second house.
        assign_value(2, birthdays, 'feb', birthdays_remaining)
        
        # Clue 7: Blends cigar and February birthday same house.
        assign_value(2, cigars, 'blends', cigars_remaining)
        
        # Clue 5: Peter is to the right of root beer (house 3) -> Peter in house 4 or 5.
        # Clue 9: Arnold is directly left of Peter -> Peter cannot be in house 4 (since house 3 is Eric), so Peter in house 5, Arnold in house 4.
        assign_value(4, names, 'Arnold', names_remaining)
        assign_value(5, names, 'Peter', names_remaining)
        
        # Clue 6: One house between January birthday and Peter (house 5) -> January birthday must be in house 3.
        assign_value(3, birthdays, 'jan', birthdays_remaining)
        
        # Clue 3: Bob has April birthday. Bob must be in house 1 (since house 2 has Alice, house 3 Eric, house 4 Arnold, house 5 Peter).
        assign_value(1, names, 'Bob', names_remaining)
        assign_value(1, birthdays, 'april', birthdays_remaining)
        
        # Remaining name Alice for house 2.
        assign_value(2, names, 'Alice', names_remaining)
        
        # Clue 12: One house between tea and coffee -> possible pairs: (1,3) invalid (house 3 root beer), (3,5) invalid, so only (2,4).
        # Clue 11: Blue Master cigar and coffee same house. Coffee cannot be in house 2 (cigar blends), so coffee in house 4, tea in house 2.
        assign_value(2, drinks, 'tea', drinks_remaining)
        assign_value(4, drinks, 'coffee', drinks_remaining)
        
        # Clue 11: Blue Master cigar in same house as coffee (house 4).
        assign_value(4, cigars, 'blue master', cigars_remaining)
        
        # Clue 10: Milk not in house 5 -> milk in house 1, water in house 5.
        assign_value(1, drinks, 'milk', drinks_remaining)
        assign_value(5, drinks, 'water', drinks_remaining)
        
        # Remaining birthdays: March and September for houses 4 and 5.
        # Clue 4: Dunhill cigar and March birthday same house. If house 4 has March, cigar must be Dunhill, but house 4 has Blue Master -> conflict. So house 4: September, house 5: March.
        assign_value(4, birthdays, 'sept', birthdays_remaining)
        assign_value(5, birthdays, 'mar', birthdays_remaining)
        
        # Clue 4: House 5 (March birthday) has Dunhill cigar.
        assign_value(5, cigars, 'dunhill', cigars_remaining)
        
        # Remaining cigar Prince for house 1.
        assign_value(1, cigars, 'prince', cigars_remaining)
        
    except Exception as e:
        print(f"Error during assignment: {e}")
        return

    # Check all houses are assigned
    for i in range(1, 6):
        if names[i] is None or birthdays[i] is None or cigars[i] is None or drinks[i] is None:
            print(f"House {i} has unassigned attributes")
            return

    # Prepare the solution in required JSON format
    header = ["House", "name", "birthday month", "favorite cigar", "favorite drink"]
    rows = []
    for i in range(1, 6):
        row = [str(i), names[i], birthdays[i], cigars[i], drinks[i]]
        rows.append(row)
    
    solution_dict = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()