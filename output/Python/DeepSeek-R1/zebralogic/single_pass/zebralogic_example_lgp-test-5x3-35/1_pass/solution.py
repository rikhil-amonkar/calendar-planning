import itertools
import json

def main():
    names_list = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
    mothers_list = ['Kailyn', 'Janelle', 'Aniya', 'Penny', 'Holly']
    heights_list = ['average', 'very short', 'short', 'very tall', 'tall']
    
    solution_found = None
    
    for names in itertools.permutations(names_list):
        # Clue 4: Peter not in second house (index 1)
        if names[1] == 'Peter':
            continue
        # Clue 8: Eric not in fifth house (index 4)
        if names[4] == 'Eric':
            continue
        
        for mothers in itertools.permutations(mothers_list):
            valid = True
            # Check Clue 1: Alice and Aniya must be in the same house.
            for i in range(5):
                if names[i] == 'Alice' and mothers[i] != 'Aniya':
                    valid = False
                    break
                if mothers[i] == 'Aniya' and names[i] != 'Alice':
                    valid = False
                    break
            if not valid:
                continue
                
            # Check Clue 3: Bob and Janelle must be in the same house.
            for i in range(5):
                if names[i] == 'Bob' and mothers[i] != 'Janelle':
                    valid = False
                    break
                if mothers[i] == 'Janelle' and names[i] != 'Bob':
                    valid = False
                    break
            if not valid:
                continue
                
            # Check Clue 10: Eric and Kailyn must be in the same house.
            for i in range(5):
                if names[i] == 'Eric' and mothers[i] != 'Kailyn':
                    valid = False
                    break
                if mothers[i] == 'Kailyn' and names[i] != 'Eric':
                    valid = False
                    break
            if not valid:
                continue
                
            for heights in itertools.permutations(heights_list):
                # Clue 11: The fifth house (index 4) has very short height.
                if heights[4] != 'very short':
                    continue
                    
                # Find Arnold's index for Clue 5 and Clue 6
                try:
                    arnold_index = names.index('Arnold')
                except ValueError:
                    continue
                    
                # Clue 6: Arnold must be very tall.
                if heights[arnold_index] != 'very tall':
                    continue
                    
                # Clue 5: The short person is directly left of Arnold.
                if arnold_index == 0:  # Arnold cannot be in first house
                    continue
                if heights[arnold_index - 1] != 'short':
                    continue
                    
                # Find Bob's index for Clue 7
                try:
                    bob_index = names.index('Bob')
                except ValueError:
                    continue
                    
                # Clue 7: Bob is directly left of the average height person.
                if bob_index >= 4:  # Bob cannot be in the last house
                    continue
                if heights[bob_index + 1] != 'average':
                    continue
                    
                # Find average height index for Clue 2
                try:
                    avg_index = heights.index('average')
                except ValueError:
                    continue
                    
                # Find Penny's index for Clue 2
                try:
                    penny_index = mothers.index('Penny')
                except ValueError:
                    continue
                    
                # Clue 2: Average height person is left of Penny's mother.
                if avg_index >= penny_index:
                    continue
                    
                # Find Holly's index for Clue 9
                try:
                    holly_index = mothers.index('Holly')
                except ValueError:
                    continue
                    
                # Clue 9: Very tall (Arnold) is right of Holly's mother.
                if arnold_index <= holly_index:
                    continue
                    
                solution_found = (names, mothers, heights)
                break
                
            if solution_found:
                break
        if solution_found:
            break
            
    if solution_found:
        names, mothers, heights = solution_found
        rows = []
        for i in range(5):
            rows.append([str(i+1), names[i], mothers[i], heights[i]])
        result = {
            "solution": {
                "header": ["House", "Name", "Mother", "Height"],
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()