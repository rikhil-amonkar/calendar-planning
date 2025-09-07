import json
from itertools import permutations

def main():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Alice', 'Peter', 'Eric', 'Bob', 'Arnold', 'Carol']
    cigars = ['pall mall', 'yellow monster', 'dunhill', 'blue master', 'prince', 'blends']
    music_genres = ['hip hop', 'jazz', 'country', 'pop', 'classical', 'rock']
    drinks = ['water', 'milk', 'boba tea', 'tea', 'root beer', 'coffee']
    mothers = ['Kailyn', 'Penny', 'Janelle', 'Holly', 'Sarah', 'Aniya']
    foods = ['soup', 'pizza', 'spaghetti', 'stir fry', 'stew', 'grilled cheese']

    for name_perm in permutations(names):
        # Eric is not in second house (clue 2)
        if name_perm[1] == 'Eric':
            continue
            
        # Eric is directly left of Carol (clue 5)
        try:
            eric_index = name_perm.index('Eric')
            carol_index = name_perm.index('Carol')
            if carol_index - eric_index != 1:
                continue
        except:
            continue

        for cigar_perm in permutations(cigars):
            # Peter smokes blends (clue 10)
            peter_index = name_perm.index('Peter')
            if cigar_perm[peter_index] != 'blends':
                continue
                
            # Dunhill not in second house (clue 24)
            if cigar_perm[1] == 'dunhill':
                continue

            for music_perm in permutations(music_genres):
                # Eric loves country music (clue 7)
                eric_index = name_perm.index('Eric')
                if music_perm[eric_index] != 'country':
                    continue
                    
                # Classical music in sixth house (clue 8)
                if music_perm[5] != 'classical':
                    continue
                    
                # Pop music not in third house (clue 6)
                if music_perm[2] == 'pop':
                    continue
                    
                # Grilled cheese right of rock music (clue 4)
                rock_index = music_perm.index('rock')
                
                for drink_perm in permutations(drinks):
                    # Bob drinks coffee (clue 9)
                    bob_index = name_perm.index('Bob')
                    if drink_perm[bob_index] != 'coffee':
                        continue
                        
                    # Eric drinks tea (clue 14)
                    if drink_perm[eric_index] != 'tea':
                        continue
                        
                    # Water directly left of Blue Master smoker (clue 19)
                    water_index = drink_perm.index('water')
                    blue_master_index = cigar_perm.index('blue master')
                    if blue_master_index - water_index != 1:
                        continue
                        
                    # Water drinker loves stew (clue 23)
                    if water_index != -1:  # Will be set later
                        pass

                    for mother_perm in permutations(mothers):
                        # Eric's mother is Aniya (clue 26)
                        if mother_perm[eric_index] != 'Aniya':
                            continue
                            
                        # Holly right of Carol (clue 3)
                        carol_index = name_perm.index('Carol')
                        holly_index = mother_perm.index('Holly')
                        if holly_index <= carol_index:
                            continue
                            
                        # Root beer directly left of Janelle (clue 12)
                        root_beer_index = drink_perm.index('root beer')
                        janelle_index = mother_perm.index('Janelle')
                        if janelle_index - root_beer_index != 1:
                            continue
                            
                        # Janelle loves milk (clue 25)
                        if drink_perm[janelle_index] != 'milk':
                            continue
                            
                        # Two houses between Sarah and Yellow Monster (clue 13)
                        sarah_index = mother_perm.index('Sarah')
                        yellow_monster_index = cigar_perm.index('yellow monster')
                        if abs(sarah_index - yellow_monster_index) != 3:
                            continue
                            
                        # Sarah directly left of jazz lover (clue 21)
                        jazz_index = music_perm.index('jazz')
                        if jazz_index - sarah_index != 1:
                            continue
                            
                        # Hip hop directly left of Kailyn (clue 17)
                        hip_hop_index = music_perm.index('hip hop')
                        kailyn_index = mother_perm.index('Kailyn')
                        if kailyn_index - hip_hop_index != 1:
                            continue
                            
                        # Arnold right of Kailyn (clue 18)
                        arnold_index = name_perm.index('Arnold')
                        if arnold_index <= kailyn_index:
                            continue
                            
                        # Hip hop directly left of root beer (clue 22)
                        if root_beer_index - hip_hop_index != 1:
                            continue

                        for food_perm in permutations(foods):
                            # Carol directly left of grilled cheese (clue 1)
                            grilled_cheese_index = food_perm.index('grilled cheese')
                            if grilled_cheese_index - carol_index != 1:
                                continue
                                
                            # Grilled cheese right of rock music (already have rock_index)
                            if grilled_cheese_index <= rock_index:
                                continue
                                
                            # Stew not in fifth house (clue 11)
                            stew_index = food_perm.index('stew')
                            if stew_index == 4:
                                continue
                                
                            # Water drinker loves stew (clue 23)
                            if drink_perm[stew_index] != 'water':
                                continue
                                
                            # Pall Mall right of stir fry (clue 15)
                            stir_fry_index = food_perm.index('stir fry')
                            pall_mall_index = cigar_perm.index('pall mall')
                            if pall_mall_index <= stir_fry_index:
                                continue
                                
                            # Spaghetti left of blends smoker (clue 20)
                            spaghetti_index = food_perm.index('spaghetti')
                            blends_index = cigar_perm.index('blends')
                            if spaghetti_index >= blends_index:
                                continue
                                
                            # Bob loves soup (clue 16)
                            if food_perm[bob_index] != 'soup':
                                continue
                                
                            # All constraints satisfied - found solution
                            solution = []
                            for i in range(6):
                                row = [
                                    str(i + 1),
                                    name_perm[i],
                                    cigar_perm[i],
                                    music_perm[i],
                                    drink_perm[i],
                                    mother_perm[i],
                                    food_perm[i]
                                ]
                                solution.append(row)
                            
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"],
                                    "rows": solution
                                }
                            }
                            
                            print(json.dumps(result, indent=2))
                            return

    print('{"solution": {"header": [], "rows": []}}')

if __name__ == "__main__":
    main()