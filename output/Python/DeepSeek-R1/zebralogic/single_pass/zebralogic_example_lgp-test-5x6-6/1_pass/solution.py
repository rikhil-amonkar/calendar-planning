import json

def main():
    houses = [0, 1, 2, 3, 4]
    attributes = ['name', 'vacation', 'education', 'color', 'phone', 'food']
    
    assignment = [
        {'name': None, 'vacation': None, 'education': None, 'color': None, 'phone': None, 'food': None},
        {'name': None, 'vacation': None, 'education': None, 'color': None, 'phone': None, 'food': None},
        {'name': 'Eric', 'vacation': None, 'education': 'doctorate', 'color': None, 'phone': 'samsung galaxy s21', 'food': 'pizza'},
        {'name': None, 'vacation': None, 'education': None, 'color': None, 'phone': None, 'food': None},
        {'name': None, 'vacation': None, 'education': None, 'color': None, 'phone': None, 'food': None}
    ]
    
    initial_domains = {}
    for i in houses:
        initial_domains[i] = {}
        for attr in attributes:
            if attr == 'name':
                full = ['Arnold', 'Eric', 'Alice', 'Bob', 'Peter']
            elif attr == 'vacation':
                full = ['mountain', 'city', 'cruise', 'beach', 'camping']
            elif attr == 'education':
                full = ['doctorate', 'high school', 'bachelor', 'associate', 'master']
            elif attr == 'color':
                full = ['blue', 'red', 'white', 'yellow', 'green']
            elif attr == 'phone':
                full = ['google pixel 6', 'iphone 13', 'oneplus 9', 'huawei p50', 'samsung galaxy s21']
            elif attr == 'food':
                full = ['grilled cheese', 'stir fry', 'pizza', 'spaghetti', 'stew']
            initial_domains[i][attr] = full[:]
    
    for attr in attributes:
        for i in houses:
            if assignment[i][attr] is not None:
                fixed_val = assignment[i][attr]
                for j in houses:
                    if j != i and fixed_val in initial_domains[j][attr]:
                        initial_domains[j][attr].remove(fixed_val)
    
    order = []
    for house in houses:
        for attr in attributes:
            if assignment[house][attr] is None:
                order.append((house, attr))
    
    def con1(ass):
        if ass[0]['food'] is not None:
            return ass[0]['food'] != 'stew'
        return True
        
    def con2(ass):
        stir_fry_house = None
        associate_house = None
        for i in range(5):
            if ass[i]['food'] == 'stir fry':
                stir_fry_house = i
            if ass[i]['education'] == 'associate':
                associate_house = i
        if stir_fry_house is not None and associate_house is not None:
            return abs(stir_fry_house - associate_house) == 3
        return True
        
    def con3(ass):
        for i in range(5):
            if ass[i]['education'] == 'bachelor' and ass[i]['vacation'] is not None:
                if ass[i]['vacation'] != 'mountain':
                    return False
            if ass[i]['vacation'] == 'mountain' and ass[i]['education'] is not None:
                if ass[i]['education'] != 'bachelor':
                    return False
        return True
        
    def con4(ass):
        bob_house = None
        doc_house = None
        for i in range(5):
            if ass[i]['name'] == 'Bob':
                bob_house = i
            if ass[i]['education'] == 'doctorate':
                doc_house = i
        if bob_house is not None and doc_house is not None:
            return doc_house > bob_house
        return True
        
    def con8(ass):
        for i in range(5):
            if ass[i]['education'] == 'bachelor' and ass[i]['food'] is not None:
                if ass[i]['food'] != 'stir fry':
                    return False
            if ass[i]['food'] == 'stir fry' and ass[i]['education'] is not None:
                if ass[i]['education'] != 'bachelor':
                    return False
        return True
        
    def con10(ass):
        peter_house = None
        green_house = None
        for i in range(5):
            if ass[i]['name'] == 'Peter':
                peter_house = i
            if ass[i]['color'] == 'green':
                green_house = i
        if peter_house is not None and green_house is not None:
            return green_house > peter_house
        return True
        
    def con11(ass):
        for i in range(5):
            if ass[i]['vacation'] == 'camping' and ass[i]['phone'] is not None:
                if ass[i]['phone'] != 'iphone 13':
                    return False
            if ass[i]['phone'] == 'iphone 13' and ass[i]['vacation'] is not None:
                if ass[i]['vacation'] != 'camping':
                    return False
        return True
        
    def con12(ass):
        for i in range(5):
            if ass[i]['vacation'] == 'cruise' and ass[i]['name'] is not None:
                if ass[i]['name'] != 'Alice':
                    return False
            if ass[i]['name'] == 'Alice' and ass[i]['vacation'] is not None:
                if ass[i]['vacation'] != 'cruise':
                    return False
        return True
        
    def con13(ass):
        for i in range(5):
            if ass[i]['education'] == 'high school':
                if i != 0 and i != 4:
                    return False
        return True
        
    def con14(ass):
        for i in range(5):
            if ass[i]['name'] == 'Arnold' and ass[i]['phone'] is not None:
                if ass[i]['phone'] != 'google pixel 6':
                    return False
            if ass[i]['phone'] == 'google pixel 6' and ass[i]['name'] is not None:
                if ass[i]['name'] != 'Arnold':
                    return False
        return True
        
    def con15(ass):
        huawei_house = None
        oneplus_house = None
        for i in range(5):
            if ass[i]['phone'] == 'huawei p50':
                huawei_house = i
            if ass[i]['phone'] == 'oneplus 9':
                oneplus_house = i
        if huawei_house is not None and oneplus_house is not None:
            return oneplus_house > huawei_house
        return True
        
    def con16(ass):
        for i in range(5):
            if ass[i]['name'] == 'Arnold' and ass[i]['food'] is not None:
                if ass[i]['food'] != 'grilled cheese':
                    return False
            if ass[i]['food'] == 'grilled cheese' and ass[i]['name'] is not None:
                if ass[i]['name'] != 'Arnold':
                    return False
        return True
        
    def con17(ass):
        if ass[3]['food'] is not None:
            return ass[3]['food'] != 'grilled cheese'
        return True
        
    def con18(ass):
        bachelor_house = None
        red_house = None
        for i in range(5):
            if ass[i]['education'] == 'bachelor':
                bachelor_house = i
            if ass[i]['color'] == 'red':
                red_house = i
        if bachelor_house is not None and red_house is not None:
            return abs(bachelor_house - red_house) == 3
        return True
        
    def con19(ass):
        city_house = None
        beach_house = None
        for i in range(5):
            if ass[i]['vacation'] == 'city':
                city_house = i
            if ass[i]['vacation'] == 'beach':
                beach_house = i
        if city_house is not None and beach_house is not None:
            return beach_house > city_house
        return True
        
    def con20(ass):
        if ass[1]['color'] is not None:
            return ass[1]['color'] != 'green'
        return True
        
    def con21(ass):
        peter_house = None
        blue_house = None
        for i in range(5):
            if ass[i]['name'] == 'Peter':
                peter_house = i
            if ass[i]['color'] == 'blue':
                blue_house = i
        if peter_house is not None and blue_house is not None:
            return blue_house > peter_house
        return True
        
    def con22(ass):
        camping_house = None
        yellow_house = None
        for i in range(5):
            if ass[i]['vacation'] == 'camping':
                camping_house = i
            if ass[i]['color'] == 'yellow':
                yellow_house = i
        if camping_house is not None and yellow_house is not None:
            return abs(camping_house - yellow_house) == 2
        return True

    constraints = [con1, con2, con3, con4, con8, con10, con11, con12, con13, con14, con15, con16, con17, con18, con19, con20, con21, con22]
    
    def check_constraints(ass):
        for con in constraints:
            if not con(ass):
                return False
        return True

    def dfs(ass, domains, order, idx):
        if idx >= len(order):
            return ass
            
        house, attr = order[idx]
        for value in domains[house][attr]:
            if value in [ass[i][attr] for i in range(5) if ass[i][attr] is not None and i != house]:
                continue
            old_value = ass[house][attr]
            ass[house][attr] = value
            if check_constraints(ass):
                result = dfs(ass, domains, order, idx+1)
                if result is not None:
                    return result
            ass[house][attr] = old_value
        return None

    solution_assignment = dfs(assignment, initial_domains, order, 0)
    if solution_assignment is None:
        print(json.dumps({"solution": {"header": [], "rows": []}}))
        return
    
    output_rows = []
    header = ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"]
    for i in range(5):
        house = solution_assignment[i]
        row = [
            str(i+1),
            house['name'],
            house['vacation'],
            house['education'],
            house['color'],
            house['phone'],
            house['food']
        ]
        output_rows.append(row)
    
    result_json = {
        "solution": {
            "header": header,
            "rows": output_rows
        }
    }
    print(json.dumps(result_json))

if __name__ == "__main__":
    main()