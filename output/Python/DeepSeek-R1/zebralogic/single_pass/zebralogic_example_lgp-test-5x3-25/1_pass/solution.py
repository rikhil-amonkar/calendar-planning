import itertools
import json

def main():
    names = ['Arnold', 'Bob', 'Alice', 'Eric', 'Peter']
    heights = ['very tall', 'average', 'tall', 'very short', 'short']
    foods = ['stew', 'grilled cheese', 'spaghetti', 'pizza', 'stir fry']
    
    fixed_index = 2
    fixed_house = ('Eric', 'tall', 'pizza')
    
    remaining_names = [n for n in names if n != fixed_house[0]]
    remaining_heights = [h for h in heights if h != fixed_house[1]]
    remaining_foods = [f for f in foods if f != fixed_house[2]]
    
    for names_perm in itertools.permutations(remaining_names):
        for heights_perm in itertools.permutations(remaining_heights):
            for foods_perm in itertools.permutations(remaining_foods):
                houses = [None] * 5
                houses[fixed_index] = fixed_house
                indices = [0, 1, 3, 4]
                for idx, (n, h, f) in zip(indices, zip(names_perm, heights_perm, foods_perm)):
                    houses[idx] = (n, h, f)
                
                alice_house = None
                short_house = None
                for i, house in enumerate(houses):
                    if house[0] == 'Alice':
                        alice_house = i
                    if house[1] == 'short':
                        short_house = i
                if alice_house is None or short_house is None or alice_house != short_house:
                    continue
                    
                if houses[1][1] == 'average':
                    continue
                    
                arnold_house = None
                stir_fry_house = None
                for i, house in enumerate(houses):
                    if house[0] == 'Arnold':
                        arnold_house = i
                    if house[2] == 'stir fry':
                        stir_fry_house = i
                if arnold_house is None or stir_fry_house is None or arnold_house != stir_fry_house:
                    continue
                    
                bob_index = None
                for i, house in enumerate(houses):
                    if house[0] == 'Bob':
                        bob_index = i
                if bob_index is None or bob_index <= arnold_house:
                    continue
                    
                grilled_cheese_index = None
                for i, house in enumerate(houses):
                    if house[2] == 'grilled cheese':
                        grilled_cheese_index = i
                if grilled_cheese_index is None or grilled_cheese_index <= 2:
                    continue
                    
                very_short_index = None
                for i, house in enumerate(houses):
                    if house[1] == 'very short':
                        very_short_index = i
                if very_short_index is None or very_short_index >= arnold_house:
                    continue
                    
                avg_index = None
                stew_index = None
                for i, house in enumerate(houses):
                    if house[1] == 'average':
                        avg_index = i
                    if house[2] == 'stew':
                        stew_index = i
                if avg_index is None or stew_index is None or avg_index >= stew_index:
                    continue
                    
                rows = []
                for i, house in enumerate(houses):
                    rows.append([str(i+1), house[0], house[1], house[2]])
                
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Height", "Food"],
                        "rows": rows
                    }
                }
                print(json.dumps(solution))
                return
                
    print('{"solution": {"header": ["House", "Name", "Height", "Food"], "rows": []}}')

if __name__ == '__main__':
    main()