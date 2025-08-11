import json

def main():
    attributes = {
        'Name': ['Arnold', 'Eric'],
        'Sport': ['basketball', 'soccer'],
        'Hair': ['brown', 'black'],
        'Height': ['very short', 'short'],
        'Smoothie': ['desert', 'cherry'],
        'Flower': ['daffodils', 'carnations']
    }
    keys = ['Name', 'Sport', 'Hair', 'Height', 'Smoothie', 'Flower']
    
    solutions = []
    
    name_list = attributes['Name']
    sport_list = attributes['Sport']
    hair_list = attributes['Hair']
    height_list = attributes['Height']
    smoothie_list = attributes['Smoothie']
    flower_list = attributes['Flower']
    
    for name1 in name_list:
        name2 = next(x for x in name_list if x != name1)
        for sport1 in sport_list:
            sport2 = next(x for x in sport_list if x != sport1)
            for hair1 in hair_list:
                hair2 = next(x for x in hair_list if x != hair1)
                for height1 in height_list:
                    height2 = next(x for x in height_list if x != height1)
                    for smoothie1 in smoothie_list:
                        smoothie2 = next(x for x in smoothie_list if x != smoothie1)
                        for flower1 in flower_list:
                            flower2 = next(x for x in flower_list if x != flower1)
                            house1 = {
                                'Name': name1,
                                'Sport': sport1,
                                'Hair': hair1,
                                'Height': height1,
                                'Smoothie': smoothie1,
                                'Flower': flower1
                            }
                            house2 = {
                                'Name': name2,
                                'Sport': sport2,
                                'Hair': hair2,
                                'Height': height2,
                                'Smoothie': smoothie2,
                                'Flower': flower2
                            }
                            if check_solution([house1, house2]):
                                solutions.append([house1, house2])
    
    if not solutions:
        print(json.dumps({"solution": {"header": [], "rows": []}}))
        return
    
    sol = solutions[0]
    header = ["House"] + keys
    rows = []
    for i, house in enumerate(sol, start=1):
        row = [str(i)]
        for key in keys:
            row.append(house[key])
        rows.append(row)
    
    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(result))

def check_solution(houses):
    if houses[1]['Sport'] == 'soccer':
        return False
    
    if houses[0]['Smoothie'] != 'desert' or houses[1]['Height'] != 'very short':
        return False
    
    if houses[1]['Hair'] != 'brown':
        return False
    
    if houses[0]['Flower'] != 'carnations':
        return False
    
    if houses[0]['Name'] != 'Eric':
        return False
    
    return True

if __name__ == "__main__":
    main()