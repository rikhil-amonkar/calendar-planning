import itertools
import json

def main():
    names = ['Eric', 'Peter', 'Arnold']
    mothers = ['Holly', 'Aniya', 'Janelle']
    foods = ['pizza', 'grilled cheese', 'spaghetti']
    
    def check_constraints(houses):
        grilled_house = None
        spaghetti_house = None
        peter_house = None
        aniya_house = None
        
        for i, house in enumerate(houses):
            if house['Food'] == 'grilled cheese':
                grilled_house = i
            if house['Food'] == 'spaghetti':
                spaghetti_house = i
            if house['Name'] == 'Peter':
                peter_house = i
            if house['Mother'] == 'Aniya':
                aniya_house = i
                
        if grilled_house is None or spaghetti_house is None or peter_house is None or aniya_house is None:
            return False
            
        if houses[grilled_house]['Name'] != 'Eric':
            return False
            
        if houses[peter_house]['Mother'] != 'Holly':
            return False
            
        if grilled_house + 1 != aniya_house:
            return False
            
        if abs(spaghetti_house - peter_house) != 1:
            return False
            
        return True

    for name_perm in itertools.permutations(names):
        for mother_perm in itertools.permutations(mothers):
            for food_perm in itertools.permutations(foods):
                houses = [
                    {'Name': name_perm[0], 'Mother': mother_perm[0], 'Food': food_perm[0]},
                    {'Name': name_perm[1], 'Mother': mother_perm[1], 'Food': food_perm[1]},
                    {'Name': name_perm[2], 'Mother': mother_perm[2], 'Food': food_perm[2]}
                ]
                
                if check_constraints(houses):
                    result = {
                        "solution": {
                            "header": ["House", "Name", "Mother", "Food"],
                            "rows": [
                                ["1", houses[0]['Name'], houses[0]['Mother'], houses[0]['Food']],
                                ["2", houses[1]['Name'], houses[1]['Mother'], houses[1]['Food']],
                                ["3", houses[2]['Name'], houses[2]['Mother'], houses[2]['Food']]
                            ]
                        }
                    }
                    print(json.dumps(result))
                    return
                    
    print('{"solution": {"header": ["House", "Name", "Mother", "Food"], "rows": []}}')

if __name__ == "__main__":
    main()