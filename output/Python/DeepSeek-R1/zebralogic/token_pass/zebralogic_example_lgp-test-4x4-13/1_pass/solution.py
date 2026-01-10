import itertools
import json

def main():
    names = ['Alice', 'Peter', 'Arnold', 'Eric']
    cigars = ['prince', 'dunhill', 'blue master', 'pall mall']
    sports = ['swimming', 'basketball', 'soccer', 'tennis']
    drinks = ['coffee', 'water', 'milk', 'tea']
    
    # Pre-filter permutations based on fixed constraints
    names_perms = [p for p in itertools.permutations(names) if p[3] == 'Peter']
    sports_perms = [p for p in itertools.permutations(sports) if p[2] == 'basketball']
    cigars_perms = [p for p in itertools.permutations(cigars) if p[3] == 'pall mall']
    drinks_perms = [p for p in itertools.permutations(drinks) if p[0] == 'water']
    
    for n in names_perms:
        for cig in cigars_perms:
            for sp in sports_perms:
                for dr in drinks_perms:
                    assignment = [
                        {'name': n[0], 'cigar': cig[0], 'sport': sp[0], 'drink': dr[0]},
                        {'name': n[1], 'cigar': cig[1], 'sport': sp[1], 'drink': dr[1]},
                        {'name': n[2], 'cigar': cig[2], 'sport': sp[2], 'drink': dr[2]},
                        {'name': n[3], 'cigar': cig[3], 'sport': sp[3], 'drink': dr[3]}
                    ]
                    
                    # Check constraints
                    # Constraint 2: Tea drinker loves basketball
                    tea_house = next((h for h in assignment if h['drink'] == 'tea'), None)
                    if not tea_house or tea_house['sport'] != 'basketball':
                        continue
                    
                    # Constraint 3: Arnold smokes Blue Master
                    arnold_house = next((h for h in assignment if h['name'] == 'Arnold'), None)
                    if not arnold_house or arnold_house['cigar'] != 'blue master':
                        continue
                    
                    # Constraint 4: Basketball lover is Eric
                    basketball_house = next((h for h in assignment if h['sport'] == 'basketball'), None)
                    if not basketball_house or basketball_house['name'] != 'Eric':
                        continue
                    
                    # Constraint 5: Tennis lover smokes Blue Master
                    tennis_house = next((h for h in assignment if h['sport'] == 'tennis'), None)
                    if not tennis_house or tennis_house['cigar'] != 'blue master':
                        continue
                    
                    # Constraint 7: Coffee drinker is Arnold
                    coffee_house = next((h for h in assignment if h['drink'] == 'coffee'), None)
                    if not coffee_house or coffee_house['name'] != 'Arnold':
                        continue
                    
                    # Constraint 9: Prince smoker loves soccer
                    prince_house = next((h for h in assignment if h['cigar'] == 'prince'), None)
                    if not prince_house or prince_house['sport'] != 'soccer':
                        continue
                    
                    # All constraints passed, build solution
                    rows = []
                    for i, house in enumerate(assignment):
                        rows.append([
                            str(i+1),
                            house['name'],
                            house['cigar'],
                            house['sport'],
                            house['drink']
                        ])
                    
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
                            "rows": rows
                        }
                    }
                    
                    print(json.dumps(solution, indent=2))
                    return
    
    print("No solution found")

if __name__ == "__main__":
    main()