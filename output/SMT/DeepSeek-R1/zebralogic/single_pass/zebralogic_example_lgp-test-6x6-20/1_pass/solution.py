from z3 import *
import json

def main():
    s = Solver()

    houses = [1, 2, 3, 4, 5, 6]

    name = {i: Int(f'name_{i}') for i in houses}
    cigar = {i: Int(f'cigar_{i}') for i in houses}
    music = {i: Int(f'music_{i}') for i in houses}
    drink = {i: Int(f'drink_{i}') for i in houses}
    mother = {i: Int(f'mother_{i}') for i in houses}
    food = {i: Int(f'food_{i}') for i in houses}

    names = ['Alice', 'Peter', 'Eric', 'Bob', 'Arnold', 'Carol']
    cigars = ['pall mall', 'yellow monster', 'dunhill', 'blue master', 'prince', 'blends']
    music_genres = ['hip hop', 'jazz', 'country', 'pop', 'classical', 'rock']
    drinks = ['water', 'milk', 'boba tea', 'tea', 'root beer', 'coffee']
    mothers = ['Kailyn', 'Penny', 'Janelle', 'Holly', 'Sarah', 'Aniya']
    foods = ['soup', 'pizza', 'spaghetti', 'stir fry', 'stew', 'grilled cheese']

    Alice_idx = 0; Peter_idx = 1; Eric_idx = 2; Bob_idx = 3; Arnold_idx = 4; Carol_idx = 5
    pall_mall_idx = 0; yellow_monster_idx = 1; dunhill_idx = 2; blue_master_idx = 3; prince_idx = 4; blends_idx = 5
    hip_hop_idx = 0; jazz_idx = 1; country_idx = 2; pop_idx = 3; classical_idx = 4; rock_idx = 5
    water_idx = 0; milk_idx = 1; boba_tea_idx = 2; tea_idx = 3; root_beer_idx = 4; coffee_idx = 5
    Kailyn_idx = 0; Penny_idx = 1; Janelle_idx = 2; Holly_idx = 3; Sarah_idx = 4; Aniya_idx = 5
    soup_idx = 0; pizza_idx = 1; spaghetti_idx = 2; stir_fry_idx = 3; stew_idx = 4; grilled_cheese_idx = 5

    for i in houses:
        s.add(And(name[i] >= 0, name[i] < 6))
        s.add(And(cigar[i] >= 0, cigar[i] < 6))
        s.add(And(music[i] >= 0, music[i] < 6))
        s.add(And(drink[i] >= 0, drink[i] < 6))
        s.add(And(mother[i] >= 0, mother[i] < 6))
        s.add(And(food[i] >= 0, food[i] < 6))
    
    s.add(Distinct([name[i] for i in houses]))
    s.add(Distinct([cigar[i] for i in houses]))
    s.add(Distinct([music[i] for i in houses]))
    s.add(Distinct([drink[i] for i in houses]))
    s.add(Distinct([mother[i] for i in houses]))
    s.add(Distinct([food[i] for i in houses]))

    # Clue 1
    s.add(Or([And(name[i] == Carol_idx, food[i+1] == grilled_cheese_idx) for i in range(1,6)]))
    
    # Clue 2
    s.add(name[2] != Eric_idx)
    
    # Clue 3
    for i in range(1,6):
        s.add(Implies(name[i] == Carol_idx, Or([mother[j] == Holly_idx for j in range(i+1,7)])))
    
    # Clue 4
    for i in range(1,6):
        s.add(Implies(music[i] == rock_idx, Or([food[j] == grilled_cheese_idx for j in range(i+1,7)])))
    
    # Clue 5
    s.add(Or([And(name[i] == Eric_idx, name[i+1] == Carol_idx) for i in range(1,6)]))
    
    # Clue 6
    s.add(music[3] != pop_idx)
    
    # Clue 7
    s.add(Or([And(name[i] == Eric_idx, music[i] == country_idx) for i in houses]))
    
    # Clue 8
    s.add(music[6] == classical_idx)
    
    # Clue 9
    s.add(Or([And(name[i] == Bob_idx, drink[i] == coffee_idx) for i in houses]))
    
    # Clue 10
    s.add(Or([And(name[i] == Peter_idx, cigar[i] == blends_idx) for i in houses]))
    
    # Clue 11
    s.add(food[5] != stew_idx)
    
    # Clue 12
    s.add(Or([And(drink[i] == root_beer_idx, mother[i+1] == Janelle_idx) for i in range(1,6)]))
    
    # Clue 13
    s.add(Or(
        Or([And(mother[i] == Sarah_idx, cigar[i+3] == yellow_monster_idx) for i in [1,2,3]]),
        Or([And(cigar[i] == yellow_monster_idx, mother[i+3] == Sarah_idx) for i in [1,2,3]])
    ))
    
    # Clue 14
    s.add(Or([And(name[i] == Eric_idx, drink[i] == tea_idx) for i in houses]))
    
    # Clue 15
    for i in range(1,6):
        s.add(Implies(food[i] == stir_fry_idx, Or([cigar[j] == pall_mall_idx for j in range(i+1,7)])))
    
    # Clue 16
    s.add(Or([And(name[i] == Bob_idx, food[i] == soup_idx) for i in houses]))
    
    # Clue 17
    s.add(Or([And(music[i] == hip_hop_idx, mother[i+1] == Kailyn_idx) for i in range(1,6)]))
    
    # Clue 18
    for i in range(1,6):
        s.add(Implies(mother[i] == Kailyn_idx, Or([name[j] == Arnold_idx for j in range(i+1,7)])))
    
    # Clue 19
    s.add(Or([And(drink[i] == water_idx, cigar[i+1] == blue_master_idx) for i in range(1,6)]))
    
    # Clue 20
    for i in range(1,6):
        s.add(Implies(food[i] == spaghetti_idx, Or([cigar[j] == blends_idx for j in range(i+1,7)])))
    
    # Clue 21
    s.add(Or([And(mother[i] == Sarah_idx, music[i+1] == jazz_idx) for i in range(1,6)]))
    
    # Clue 22
    s.add(Or([And(music[i] == hip_hop_idx, drink[i+1] == root_beer_idx) for i in range(1,6)]))
    
    # Clue 23
    s.add(Or([And(drink[i] == water_idx, food[i] == stew_idx) for i in houses]))
    
    # Clue 24
    s.add(cigar[2] != dunhill_idx)
    
    # Clue 25
    s.add(Or([And(drink[i] == milk_idx, mother[i] == Janelle_idx) for i in houses]))
    
    # Clue 26
    s.add(Or([And(name[i] == Eric_idx, mother[i] == Aniya_idx) for i in houses]))

    if s.check() == sat:
        m = s.model()
        solution_rows = []
        for i in houses:
            name_val = m[name[i]].as_long()
            cigar_val = m[cigar[i]].as_long()
            music_val = m[music[i]].as_long()
            drink_val = m[drink[i]].as_long()
            mother_val = m[mother[i]].as_long()
            food_val = m[food[i]].as_long()
            row = [
                str(i),
                names[name_val],
                cigars[cigar_val],
                music_genres[music_val],
                drinks[drink_val],
                mothers[mother_val],
                foods[food_val]
            ]
            solution_rows.append(row)
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"],
                "rows": solution_rows
            }
        }
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()