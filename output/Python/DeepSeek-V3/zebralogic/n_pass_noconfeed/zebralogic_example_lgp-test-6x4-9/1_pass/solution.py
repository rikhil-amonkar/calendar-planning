import json
from itertools import permutations

def main():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Carol', 'Bob', 'Alice', 'Arnold', 'Eric', 'Peter']
    phones = ['samsung galaxy s21', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9', 'xiaomi mi 11']
    nationalities = ['swede', 'chinese', 'norwegian', 'dane', 'german', 'brit']
    colors = ['blue', 'red', 'yellow', 'green', 'white', 'purple']
    
    for name_perm in permutations(names):
        for phone_perm in permutations(phones):
            for nat_perm in permutations(nationalities):
                for color_perm in permutations(colors):
                    assignment = {}
                    for i, house in enumerate(houses):
                        assignment[house] = {
                            'name': name_perm[i],
                            'phone': phone_perm[i],
                            'nationality': nat_perm[i],
                            'color': color_perm[i]
                        }
                    
                    # Check all constraints
                    # 1. Carol is not in the third house.
                    if assignment[3]['name'] == 'Carol':
                        continue
                    
                    # 2. There is one house between the Dane and the British person.
                    dane_house = None
                    brit_house = None
                    for house in houses:
                        if assignment[house]['nationality'] == 'dane':
                            dane_house = house
                        if assignment[house]['nationality'] == 'brit':
                            brit_house = house
                    if dane_house is None or brit_house is None or abs(dane_house - brit_house) != 2:
                        continue
                    
                    # 3. Carol is the person whose favorite color is green.
                    carol_house = None
                    green_house = None
                    for house in houses:
                        if assignment[house]['name'] == 'Carol':
                            carol_house = house
                        if assignment[house]['color'] == 'green':
                            green_house = house
                    if carol_house != green_house:
                        continue
                    
                    # 4. Arnold is directly left of Alice.
                    arnold_house = None
                    alice_house = None
                    for house in houses:
                        if assignment[house]['name'] == 'Arnold':
                            arnold_house = house
                        if assignment[house]['name'] == 'Alice':
                            alice_house = house
                    if arnold_house is None or alice_house is None or arnold_house + 1 != alice_house:
                        continue
                    
                    # 5. Alice is the German.
                    if assignment[alice_house]['nationality'] != 'german':
                        continue
                    
                    # 6. The person who uses a OnePlus 9 is the person who loves purple.
                    oneplus_house = None
                    purple_house = None
                    for house in houses:
                        if assignment[house]['phone'] == 'oneplus 9':
                            oneplus_house = house
                        if assignment[house]['color'] == 'purple':
                            purple_house = house
                    if oneplus_house != purple_house:
                        continue
                    
                    # 7. The person who uses a Huawei P50 is not in the third house.
                    if assignment[3]['phone'] == 'huawei p50':
                        continue
                    
                    # 8. The person who uses a Samsung Galaxy S21 is in the fifth house.
                    if assignment[5]['phone'] != 'samsung galaxy s21':
                        continue
                    
                    # 9. The person who loves white is somewhere to the right of the person whose favorite color is red.
                    white_house = None
                    red_house = None
                    for house in houses:
                        if assignment[house]['color'] == 'white':
                            white_house = house
                        if assignment[house]['color'] == 'red':
                            red_house = house
                    if white_house is None or red_house is None or white_house <= red_house:
                        continue
                    
                    # 10. The person who uses a Samsung Galaxy S21 is Bob.
                    if assignment[5]['name'] != 'Bob':
                        continue
                    
                    # 11. The Dane is the person who loves yellow.
                    if assignment[dane_house]['color'] != 'yellow':
                        continue
                    
                    # 12. The person who uses a Samsung Galaxy S21 is somewhere to the left of Peter.
                    peter_house = None
                    for house in houses:
                        if assignment[house]['name'] == 'Peter':
                            peter_house = house
                    if peter_house is None or peter_house <= 5:
                        continue
                    
                    # 13. The person who loves blue is Peter.
                    blue_house = None
                    for house in houses:
                        if assignment[house]['color'] == 'blue':
                            blue_house = house
                    if blue_house != peter_house:
                        continue
                    
                    # 14. Peter is the British person.
                    if assignment[peter_house]['nationality'] != 'brit':
                        continue
                    
                    # 15. The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
                    iphone_house = None
                    for house in houses:
                        if assignment[house]['phone'] == 'iphone 13':
                            iphone_house = house
                    if iphone_house != 6:
                        continue
                    
                    # 16. The Norwegian is the person who loves purple.
                    norwegian_house = None
                    for house in houses:
                        if assignment[house]['nationality'] == 'norwegian':
                            norwegian_house = house
                    if norwegian_house != purple_house:
                        continue
                    
                    # 17. The person who uses a Xiaomi Mi 11 is the Chinese.
                    xiaomi_house = None
                    for house in houses:
                        if assignment[house]['phone'] == 'xiaomi mi 11':
                            xiaomi_house = house
                    chinese_house = None
                    for house in houses:
                        if assignment[house]['nationality'] == 'chinese':
                            chinese_house = house
                    if xiaomi_house != chinese_house:
                        continue
                    
                    # If we get here, all constraints are satisfied
                    result = {"solution": {"header": ["House", "Name", "PhoneModel", "Nationality", "Color"], "rows": []}}
                    for house in houses:
                        row = [
                            str(house),
                            assignment[house]['name'],
                            assignment[house]['phone'],
                            assignment[house]['nationality'],
                            assignment[house]['color']
                        ]
                        result["solution"]["rows"].append(row)
                    
                    print(json.dumps(result, indent=2))
                    return
    
    print(json.dumps({"solution": {"header": ["House", "Name", "PhoneModel", "Nationality", "Color"], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()