import json

def main():
    attributes_dict = {
        'Name': ['Arnold', 'Eric'],
        'Occupation': ['engineer', 'doctor'],
        'Birthday': ['april', 'sept'],
        'HouseStyle': ['victorian', 'colonial'],
        'Height': ['very short', 'short'],
        'Cigar': ['pall mall', 'prince']
    }
    
    solutions = []
    
    for name1 in attributes_dict['Name']:
        name2 = next(x for x in attributes_dict['Name'] if x != name1)
        for occ1 in attributes_dict['Occupation']:
            occ2 = next(x for x in attributes_dict['Occupation'] if x != occ1)
            for bd1 in attributes_dict['Birthday']:
                bd2 = next(x for x in attributes_dict['Birthday'] if x != bd1)
                for hs1 in attributes_dict['HouseStyle']:
                    hs2 = next(x for x in attributes_dict['HouseStyle'] if x != hs1)
                    for ht1 in attributes_dict['Height']:
                        ht2 = next(x for x in attributes_dict['Height'] if x != ht1)
                        for cg1 in attributes_dict['Cigar']:
                            cg2 = next(x for x in attributes_dict['Cigar'] if x != cg1)
                            
                            house1 = {
                                'Name': name1,
                                'Occupation': occ1,
                                'Birthday': bd1,
                                'HouseStyle': hs1,
                                'Height': ht1,
                                'Cigar': cg1
                            }
                            house2 = {
                                'Name': name2,
                                'Occupation': occ2,
                                'Birthday': bd2,
                                'HouseStyle': hs2,
                                'Height': ht2,
                                'Cigar': cg2
                            }
                            
                            # Constraint 1: Engineer in first house
                            if house1['Occupation'] != 'engineer':
                                continue
                            
                            # Constraint 6: Engineer is Eric
                            if house1['Name'] != 'Eric':
                                continue
                            
                            # Constraint 3: Colonial house is engineer
                            if house1['HouseStyle'] == 'colonial':
                                pass
                            elif house2['HouseStyle'] == 'colonial':
                                if house2['Occupation'] != 'engineer':
                                    continue
                            else:
                                continue
                            
                            # Constraint 4: Very short is engineer
                            if house1['Height'] == 'very short':
                                pass
                            elif house2['Height'] == 'very short':
                                if house2['Occupation'] != 'engineer':
                                    continue
                            else:
                                continue
                            
                            # Constraint 5: Short person smokes Pall Mall
                            if house1['Height'] == 'short':
                                if house1['Cigar'] != 'pall mall':
                                    continue
                            else:
                                if house2['Height'] != 'short' or house2['Cigar'] != 'pall mall':
                                    continue
                            
                            # Constraint 2: April birthday and doctor in different houses
                            april_house = 1 if house1['Birthday'] == 'april' else 2
                            doctor_house = 1 if house1['Occupation'] == 'doctor' else 2
                            if april_house == doctor_house:
                                continue
                            
                            solutions.append((house1, house2))
    
    header = ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"]
    if solutions:
        house1, house2 = solutions[0]
        rows = [
            ["1", house1['Name'], house1['Occupation'], house1['Birthday'], house1['HouseStyle'], house1['Height'], house1['Cigar']],
            ["2", house2['Name'], house2['Occupation'], house2['Birthday'], house2['HouseStyle'], house2['Height'], house2['Cigar']]
        ]
    else:
        rows = []
    
    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()