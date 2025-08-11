import json

def check_house(house):
    name = house['name']
    smoothie = house['smoothie']
    sport = house['sport']
    car = house['car']
    flower = house['flower']
    
    if name == 'Eric':
        if car != 'tesla model 3' or flower != 'roses':
            return False
    if car == 'tesla model 3':
        if name != 'Eric' or flower != 'roses':
            return False
    if flower == 'roses':
        if name != 'Eric' or car != 'tesla model 3':
            return False
            
    if name == 'Peter':
        if smoothie != 'dragonfruit':
            return False
            
    if name == 'Arnold':
        if sport != 'basketball' or flower != 'lilies':
            return False
    if sport == 'basketball':
        if name != 'Arnold' or flower != 'lilies':
            return False
    if flower == 'lilies':
        if name != 'Arnold' or sport != 'basketball':
            return False
            
    if smoothie == 'desert':
        if car != 'toyota camry':
            return False
            
    if car == 'honda civic':
        if flower != 'daffodils':
            return False
            
    return True

def check_global(assignment):
    toyota_index = None
    arnold_index = None
    honda_index = None
    desert_index = None
    
    for idx, house in enumerate(assignment):
        if house['car'] == 'toyota camry':
            toyota_index = idx
        if house['name'] == 'Arnold':
            arnold_index = idx
        if house['car'] == 'honda civic':
            honda_index = idx
        if house['smoothie'] == 'desert':
            desert_index = idx
            
    if toyota_index is None or arnold_index is None or honda_index is None or desert_index is None:
        return False
        
    if abs(toyota_index - arnold_index) != 1:
        return False
        
    if honda_index <= desert_index:
        return False
        
    return True

def backtrack(assignment, available_names, available_smoothies, available_sports, available_cars, available_flowers, index):
    if index == 4:
        if check_global(assignment):
            return assignment
        else:
            return None
            
    if index == 0:
        sport = 'tennis'
    elif index == 1:
        sport = 'soccer'
    else:
        sport = None
        
    if index < 2:
        for name in list(available_names):
            if name == 'Arnold':
                continue
                
            if name == 'Eric':
                car_list = ['tesla model 3']
                flower_list = ['roses']
            elif name == 'Peter':
                car_list = list(available_cars)
                flower_list = list(available_flowers)
            else:
                car_list = list(available_cars)
                flower_list = list(available_flowers)
                
            for smoothie in list(available_smoothies):
                if index == 0 and smoothie == 'watermelon':
                    continue
                if name == 'Peter' and smoothie != 'dragonfruit':
                    continue
                    
                if smoothie == 'desert':
                    if 'toyota camry' in car_list:
                        car_list2 = ['toyota camry']
                    else:
                        car_list2 = []
                else:
                    car_list2 = car_list
                    
                for car in car_list2:
                    if car == 'honda civic':
                        if 'daffodils' in flower_list:
                            flower_list2 = ['daffodils']
                        else:
                            flower_list2 = []
                    else:
                        flower_list2 = flower_list
                        
                    for flower in flower_list2:
                        candidate = {
                            'name': name,
                            'smoothie': smoothie,
                            'sport': sport,
                            'car': car,
                            'flower': flower
                        }
                        if not check_house(candidate):
                            continue
                            
                        new_available_names = available_names - {name}
                        new_available_smoothies = available_smoothies - {smoothie}
                        new_available_sports = available_sports - {sport}
                        new_available_cars = available_cars - {car}
                        new_available_flowers = available_flowers - {flower}
                        
                        assignment.append(candidate)
                        result = backtrack(assignment, new_available_names, new_available_smoothies, new_available_sports, new_available_cars, new_available_flowers, index+1)
                        if result is not None:
                            return result
                        assignment.pop()
        return None
        
    else:
        for sport_val in list(available_sports):
            for name in list(available_names):
                if name == 'Eric':
                    car_list = ['tesla model 3']
                    flower_list = ['roses']
                elif name == 'Arnold':
                    if sport_val != 'basketball':
                        continue
                    car_list = list(available_cars)
                    flower_list = ['lilies']
                elif name == 'Peter':
                    car_list = list(available_cars)
                    flower_list = list(available_flowers)
                else:
                    car_list = list(available_cars)
                    flower_list = list(available_flowers)
                    
                for smoothie in list(available_smoothies):
                    if name == 'Peter' and smoothie != 'dragonfruit':
                        continue
                    if smoothie == 'desert':
                        if 'toyota camry' in car_list:
                            car_list2 = ['toyota camry']
                        else:
                            car_list2 = []
                    else:
                        car_list2 = car_list
                        
                    for car in car_list2:
                        if car == 'honda civic':
                            if 'daffodils' in flower_list:
                                flower_list2 = ['daffodils']
                            else:
                                flower_list2 = []
                        else:
                            flower_list2 = flower_list
                            
                        for flower in flower_list2:
                            candidate = {
                                'name': name,
                                'smoothie': smoothie,
                                'sport': sport_val,
                                'car': car,
                                'flower': flower
                            }
                            if not check_house(candidate):
                                continue
                                
                            new_available_names = available_names - {name}
                            new_available_smoothies = available_smoothies - {smoothie}
                            new_available_sports = available_sports - {sport_val}
                            new_available_cars = available_cars - {car}
                            new_available_flowers = available_flowers - {flower}
                            
                            assignment.append(candidate)
                            result = backtrack(assignment, new_available_names, new_available_smoothies, new_available_sports, new_available_cars, new_available_flowers, index+1)
                            if result is not None:
                                return result
                            assignment.pop()
        return None

def main():
    names = set(['Eric', 'Alice', 'Peter', 'Arnold'])
    smoothies = set(['dragonfruit', 'cherry', 'desert', 'watermelon'])
    sports = set(['soccer', 'tennis', 'basketball', 'swimming'])
    cars = set(['tesla model 3', 'toyota camry', 'honda civic', 'ford f150'])
    flowers = set(['daffodils', 'roses', 'lilies', 'carnations'])
    
    assignment = []
    sol = backtrack(assignment, names, smoothies, sports, cars, flowers, 0)
    if sol is None:
        print('{"error": "No solution found"}')
        return
        
    header = ["House", "Name", "Smoothie", "Sport", "Car", "Flower"]
    rows = []
    for i, house in enumerate(sol):
        row = [str(i+1), house['name'], house['smoothie'], house['sport'], house['car'], house['flower']]
        rows.append(row)
        
    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(result))

if __name__ == '__main__':
    main()