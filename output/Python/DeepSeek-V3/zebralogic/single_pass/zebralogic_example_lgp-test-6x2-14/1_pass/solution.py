import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each attribute
    names = ['Carol', 'Peter', 'Eric', 'Arnold', 'Alice', 'Bob']
    cigars = ['blends', 'yellow monster', 'pall mall', 'blue master', 'dunhill', 'prince']
    
    # There are 6 houses, numbered 1 to 6
    houses = [1, 2, 3, 4, 5, 6]
    
    # We'll represent each house as a dictionary with attributes
    # Initialize all possible permutations (though this is brute force and not efficient)
    # Instead, we'll use constraint satisfaction
    
    # Let's approach this systematically
    
    # Initialize the solution structure
    solution = {
        "solution": {
            "header": ["House", "Name", "cigar"],
            "rows": []
        }
    }
    
    # We'll create a list to hold the assignments for each house
    assignments = [{} for _ in houses]
    
    # Apply the direct assignments first
    # Clue 8: Peter is in the first house
    assignments[0]['Name'] = 'Peter'
    # Clue 6: Eric is in the sixth house
    assignments[5]['Name'] = 'Eric'
    # Clue 9: Bob is in the third house
    assignments[2]['Name'] = 'Bob'
    # Clue 5: The person partial to Pall Mall is in the third house
    assignments[2]['cigar'] = 'pall mall'
    # Clue 2: The person who smokes Blue Master is in the fifth house
    assignments[4]['cigar'] = 'blue master'
    
    # Now process the other clues
    
    # Clue 7: Carol and Eric are next to each other
    # Eric is in house 6, so Carol must be in house 5
    assignments[4]['Name'] = 'Carol'
    
    # Remaining names: Arnold, Alice
    # Clue 3: Arnold is somewhere to the left of the Prince smoker
    # Clue 1: Arnold is somewhere to the left of the person who smokes blends
    
    # Clue 4: There is one house between the person who smokes Yellow Monster and the person who smokes blends
    # This means if yellow monster is in X, blends is in X+2, or blends is in X, yellow monster is in X-2
    # But since Arnold is left of blends (clue 1), and Arnold is not in house 6,5,3,1 (Peter is in 1, Bob in 3, Carol in 5, Eric in 6)
    # So Arnold is in house 2 or 4
    # Let's try Arnold in house 2
    assignments[1]['Name'] = 'Arnold'
    # Then Alice must be in house 4
    assignments[3]['Name'] = 'Alice'
    
    # Now assign cigars
    # We have assigned pall mall to house 3, blue master to house 5
    # Remaining cigars: blends, yellow monster, dunhill, prince
    
    # From clue 4: one house between yellow monster and blends
    # Possible positions:
    # yellow in 1, blends in 3 - but 3 is pall mall
    # yellow in 2, blends in 4
    # yellow in 3, blends in 5 - but 3 is pall mall, 5 is blue master
    # yellow in 4, blends in 6
    # So possible: yellow in 2, blends in 4 or yellow in 4, blends in 6
    
    # From clue 1: Arnold is left of blends. Arnold is in 2, so blends must be right of 2
    # So blends can be in 3,4,5,6. But 3 is pall mall, 5 is blue master, so blends in 4 or 6
    # From clue 4: if blends is in 4, yellow is in 2
    # if blends is in 6, yellow is in 4
    
    # From clue 3: Arnold is left of prince smoker. Arnold is in 2, so prince is right of 2
    # So prince is in 3,4,5,6. But 3 is pall mall, 5 is blue master, so prince in 4 or 6
    
    # Let's try blends in 4, yellow in 2
    assignments[1]['cigar'] = 'yellow monster'
    assignments[3]['cigar'] = 'blends'
    # Now prince must be right of 2, so 4 or 6
    # 4 is blends, so prince in 6
    assignments[5]['cigar'] = 'prince'
    # Remaining cigar: dunhill in house 1
    assignments[0]['cigar'] = 'dunhill'
    
    # Check all clues:
    # 1. Arnold (2) left of blends (4) - yes
    # 2. blue master in 5 - yes
    # 3. Arnold (2) left of prince (6) - yes
    # 4. one house between yellow (2) and blends (4) - yes (3 in between)
    # 5. pall mall in 3 - yes
    # 6. Eric in 6 - yes
    # 7. Carol (5) and Eric (6) next to each other - yes
    # 8. Peter in 1 - yes
    # 9. Bob in 3 - yes
    
    # Now build the solution
    for i in range(len(houses)):
        house_num = i + 1
        name = assignments[i].get('Name', '')
        cigar = assignments[i].get('cigar', '')
        solution["solution"]["rows"].append([str(house_num), name, cigar])
    
    return json.dumps(solution)

if __name__ == "__main__":
    print(solve_puzzle())