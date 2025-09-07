import json
from itertools import permutations

def main():
    names = ['Carol', 'Peter', 'Eric', 'Arnold', 'Alice', 'Bob']
    cigars = ['blends', 'yellow monster', 'pall mall', 'blue master', 'dunhill', 'prince']
    
    # Generate all possible permutations for names and cigars
    for name_perm in permutations(names):
        for cigar_perm in permutations(cigars):
            # Assign houses 1-6
            assignment = {}
            for i in range(6):
                house = i + 1
                assignment[house] = {
                    'name': name_perm[i],
                    'cigar': cigar_perm[i]
                }
            
            # Check all constraints
            valid = True
            
            # Clue 2: Blue Master in fifth house
            if assignment[5]['cigar'] != 'blue master':
                continue
            
            # Clue 5: Pall Mall in third house
            if assignment[3]['cigar'] != 'pall mall':
                continue
            
            # Clue 6: Eric in sixth house
            if assignment[6]['name'] != 'Eric':
                continue
            
            # Clue 8: Peter in first house
            if assignment[1]['name'] != 'Peter':
                continue
            
            # Clue 9: Bob in third house
            if assignment[3]['name'] != 'Bob':
                continue
            
            # Clue 7: Carol and Eric are next to each other
            carol_house = None
            for house, attrs in assignment.items():
                if attrs['name'] == 'Carol':
                    carol_house = house
                    break
            if carol_house is None or abs(carol_house - 6) != 1:
                continue
            
            # Clue 1: Arnold left of blends smoker
            arnold_house = None
            blends_house = None
            for house, attrs in assignment.items():
                if attrs['name'] == 'Arnold':
                    arnold_house = house
                if attrs['cigar'] == 'blends':
                    blends_house = house
            if arnold_house is None or blends_house is None or arnold_house >= blends_house:
                continue
            
            # Clue 3: Arnold left of prince smoker
            prince_house = None
            for house, attrs in assignment.items():
                if attrs['cigar'] == 'prince':
                    prince_house = house
                    break
            if prince_house is None or arnold_house >= prince_house:
                continue
            
            # Clue 4: One house between Yellow Monster and blends
            yellow_monster_house = None
            for house, attrs in assignment.items():
                if attrs['cigar'] == 'yellow monster':
                    yellow_monster_house = house
                    break
            if yellow_monster_house is None or abs(yellow_monster_house - blends_house) != 2:
                continue
            
            # If we get here, all constraints are satisfied
            solution = {
                "solution": {
                    "header": ["House", "Name", "Cigar"],
                    "rows": []
                }
            }
            
            for house in range(1, 7):
                attrs = assignment[house]
                solution["solution"]["rows"].append([
                    str(house),
                    attrs['name'],
                    attrs['cigar']
                ])
            
            print(json.dumps(solution, indent=2))
            return
    
    print('{"solution": {"header": ["House", "Name", "Cigar"], "rows": []}}')

if __name__ == "__main__":
    main()