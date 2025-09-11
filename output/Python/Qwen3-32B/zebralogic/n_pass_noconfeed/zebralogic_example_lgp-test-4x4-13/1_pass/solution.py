import itertools
import json

# Define the possible values for each category
names = ['Alice', 'Peter', 'Arnold', 'Eric']
drinks = ['coffee', 'water', 'milk', 'tea']
sports = ['swimming', 'basketball', 'soccer', 'tennis']
cigars = ['prince', 'dunhill', 'blue master', 'pall mall']

# Generate valid permutations for each category based on direct clues
valid_names_perms = [p for p in itertools.permutations(names) if p[3] == 'Peter' and p[2] == 'Eric']
valid_drinks_perms = [p for p in itertools.permutations(drinks) if p[0] == 'water' and p[2] == 'tea']
valid_sports_perms = [p for p in itertools.permutations(sports) if p[2] == 'basketball']
valid_cigar_perms = [p for p in itertools.permutations(cigars) if p[3] == 'pall mall']

# Iterate through all possible combinations of permutations
for names_p in valid_names_perms:
    for drinks_p in valid_drinks_perms:
        for sports_p in valid_sports_perms:
            for cigars_p in valid_cigar_perms:
                # Check Arnold's constraints (clues 3 and 7)
                arnold_idx = names_p.index('Arnold')
                if drinks_p[arnold_idx] != 'coffee':
                    continue
                if cigars_p[arnold_idx] != 'blue master':
                    continue
                
                # Check tennis lover smokes Blue Master (clue 5)
                try:
                    tennis_idx = sports_p.index('tennis')
                except ValueError:
                    continue  # Should not happen as per constraints
                if cigars_p[tennis_idx] != 'blue master':
                    continue
                
                # Check Prince smoker's sport is soccer (clue 9)
                prince_indices = [i for i, c in enumerate(cigars_p) if c == 'prince']
                if not prince_indices:
                    continue  # Should not happen as per permutations
                prince_idx = prince_indices[0]
                if sports_p[prince_idx] != 'soccer':
                    continue
                
                # All constraints satisfied, build the solution
                solution_rows = []
                for i in range(4):
                    house_num = str(i + 1)
                    name = names_p[i]
                    cigar = cigars_p[i]
                    sport = sports_p[i]
                    drink = drinks_p[i]
                    solution_rows.append([house_num, name, cigar, sport, drink])
                
                # Format as required JSON
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
                        "rows": solution_rows
                    }
                }
                print(json.dumps(solution))
                exit()

# If no solution found (should not happen)
print(json.dumps({"solution": {"header": [], "rows": []}}))