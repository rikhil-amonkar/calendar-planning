import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options
    names = ['Arnold', 'Bob', 'Alice', 'Eric', 'Peter']
    heights = ['very tall', 'average', 'tall', 'very short', 'short']
    foods = ['stew', 'grilled cheese', 'spaghetti', 'pizza', 'stir fry']
    houses = ['1', '2', '3', '4', '5']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for height_perm in permutations(heights):
            for food_perm in permutations(foods):
                solution = []
                valid = True
                
                # Create a list of house assignments
                for i in range(5):
                    house = {
                        'House': str(i+1),
                        'Name': name_perm[i],
                        'Height': height_perm[i],
                        'Food': food_perm[i]
                    }
                    solution.append(house)
                
                # Check all constraints
                # 1. Alice is short
                alice_house = next((h for h in solution if h['Name'] == 'Alice'), None)
                if not alice_house or alice_house['Height'] != 'short':
                    valid = False
                    continue
                
                # 2. Tall person is in house 3
                if solution[2]['Height'] != 'tall':
                    valid = False
                    continue
                
                # 3. Average height not in house 2
                if solution[1]['Height'] == 'average':
                    valid = False
                    continue
                
                # 4. Average height is left of stew
                avg_house = next((h for h in solution if h['Height'] == 'average'), None)
                stew_house = next((h for h in solution if h['Food'] == 'stew'), None)
                if not avg_house or not stew_house or int(avg_house['House']) >= int(stew_house['House']):
                    valid = False
                    continue
                
                # 5. Arnold loves stir fry
                arnold_house = next((h for h in solution if h['Name'] == 'Arnold'), None)
                if not arnold_house or arnold_house['Food'] != 'stir fry':
                    valid = False
                    continue
                
                # 6. Pizza lover is tall
                pizza_house = next((h for h in solution if h['Food'] == 'pizza'), None)
                if not pizza_house or pizza_house['Height'] != 'tall':
                    valid = False
                    continue
                
                # 7. Eric is tall
                eric_house = next((h for h in solution if h['Name'] == 'Eric'), None)
                if not eric_house or eric_house['Height'] != 'tall':
                    valid = False
                    continue
                
                # 8. Bob is right of Arnold
                bob_house = next((h for h in solution if h['Name'] == 'Bob'), None)
                if not bob_house or not arnold_house or int(bob_house['House']) <= int(arnold_house['House']):
                    valid = False
                    continue
                
                # 9. Grilled cheese is right of Eric
                gc_house = next((h for h in solution if h['Food'] == 'grilled cheese'), None)
                if not gc_house or not eric_house or int(gc_house['House']) <= int(eric_house['House']):
                    valid = False
                    continue
                
                # 10. Very short is left of Arnold
                vs_house = next((h for h in solution if h['Height'] == 'very short'), None)
                if not vs_house or not arnold_house or int(vs_house['House']) >= int(arnold_house['House']):
                    valid = False
                    continue
                
                if valid:
                    # Prepare the output
                    output = {
                        "solution": {
                            "header": ["House", "Name", "Height", "Food"],
                            "rows": []
                        }
                    }
                    for house in sorted(solution, key=lambda x: int(x['House'])):
                        output["solution"]["rows"].append([
                            house['House'],
                            house['Name'],
                            house['Height'],
                            house['Food']
                        ])
                    return output
    
    return {"solution": {"header": ["House", "Name", "Height", "Food"], "rows": []}}

# Solve and print the solution
solution = solve_puzzle()
print(json.dumps(solution, indent=2))