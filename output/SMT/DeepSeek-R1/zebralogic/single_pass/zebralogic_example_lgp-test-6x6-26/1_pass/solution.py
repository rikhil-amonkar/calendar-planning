from z3 import *

def main():
    # Define the attribute lists
    names = ['Peter', 'Carol', 'Eric', 'Alice', 'Bob', 'Arnold']
    phones = ['huawei p50', 'google pixel 6', 'xiaomi mi 11', 'iphone 13', 'samsung galaxy s21', 'oneplus 9']
    cigars = ['dunhill', 'pall mall', 'blends', 'blue master', 'prince', 'yellow monster']
    flowers = ['daffodils', 'carnations', 'roses', 'tulips', 'lilies', 'iris']
    colors = ['yellow', 'red', 'green', 'blue', 'white', 'purple']
    sports = ['soccer', 'tennis', 'basketball', 'volleyball', 'swimming', 'baseball']
    
    # Create variables for each attribute in each category
    name_vars = {name: Int(f'Name_{name}') for name in names}
    phone_vars = {phone: Int(f'Phone_{phone.replace(" ", "_")}') for phone in phones}
    cigar_vars = {cigar: Int(f'Cigar_{cigar.replace(" ", "_")}') for cigar in cigars}
    flower_vars = {flower: Int(f'Flower_{flower}') for flower in flowers}
    color_vars = {color: Int(f'Color_{color}') for color in colors}
    sport_vars = {sport: Int(f'Sport_{sport}') for sport in sports}
    
    s = Solver()
    
    # Each attribute house is between 1 and 6
    all_vars = list(name_vars.values()) + list(phone_vars.values()) + list(cigar_vars.values()) + list(flower_vars.values()) + list(color_vars.values()) + list(sport_vars.values())
    for var in all_vars:
        s.add(var >= 1, var <= 6)
    
    # Each category has distinct houses
    s.add(Distinct(list(name_vars.values())))
    s.add(Distinct(list(phone_vars.values())))
    s.add(Distinct(list(cigar_vars.values())))
    s.add(Distinct(list(flower_vars.values())))
    s.add(Distinct(list(color_vars.values())))
    s.add(Distinct(list(sport_vars.values())))
    
    # Clue 1: OnePlus 9 in house 2
    s.add(phone_vars['oneplus 9'] == 2)
    
    # Clue 2: Xiaomi left of Huawei
    s.add(phone_vars['xiaomi mi 11'] < phone_vars['huawei p50'])
    
    # Clue 3: Carol loves carnations
    s.add(name_vars['Carol'] == flower_vars['carnations'])
    
    # Clue 4: Purple left of Pall Mall
    s.add(color_vars['purple'] + 1 == cigar_vars['pall mall'])
    
    # Clue 5: Green color and Blue Master cigar same house
    s.add(color_vars['green'] == cigar_vars['blue master'])
    
    # Clue 6: Yellow and blue adjacent
    yellow_house = color_vars['yellow']
    blue_house = color_vars['blue']
    s.add(Or(yellow_house == blue_house + 1, yellow_house == blue_house - 1))
    
    # Clue 7: Eric right of Samsung user
    s.add(phone_vars['samsung galaxy s21'] < name_vars['Eric'])
    
    # Clue 8: Two houses between Carol and daffodils
    carol_house = name_vars['Carol']
    daffodils_house = flower_vars['daffodils']
    s.add(Or(carol_house == daffodils_house + 3, carol_house == daffodils_house - 3))
    
    # Clue 9: Prince smoker loves basketball
    s.add(cigar_vars['prince'] == sport_vars['basketball'])
    
    # Clue 10: Dunhill smoker loves volleyball
    s.add(cigar_vars['dunhill'] == sport_vars['volleyball'])
    
    # Clue 11: Swimming lover uses Google Pixel 6
    s.add(sport_vars['swimming'] == phone_vars['google pixel 6'])
    
    # Clue 12: Huawei P50 left of white color
    s.add(phone_vars['huawei p50'] + 1 == color_vars['white'])
    
    # Clue 13: OnePlus 9 and roses adjacent
    oneplus_house = phone_vars['oneplus 9']
    roses_house = flower_vars['roses']
    s.add(Or(oneplus_house == roses_house + 1, oneplus_house == roses_house - 1))
    
    # Clue 14: Iris left of Eric
    s.add(flower_vars['iris'] < name_vars['Eric'])
    
    # Clue 15: Dunhill smoker is Peter
    s.add(cigar_vars['dunhill'] == name_vars['Peter'])
    
    # Clue 16: Blue color is Peter
    s.add(color_vars['blue'] == name_vars['Peter'])
    
    # Clue 17: Tulips are Bob's favorite
    s.add(flower_vars['tulips'] == name_vars['Bob'])
    
    # Clue 18: Alice in house 1
    s.add(name_vars['Alice'] == 1)
    
    # Clue 19: Baseball directly left of Blue Master
    s.add(sport_vars['baseball'] + 1 == cigar_vars['blue master'])
    
    # Clue 20: Google Pixel 6 right of blends smoker
    s.add(cigar_vars['blends'] < phone_vars['google pixel 6'])
    
    # Clue 21: Soccer is Carol
    s.add(sport_vars['soccer'] == name_vars['Carol'])
    
    # Clue 22: Carnations directly left of blends
    s.add(flower_vars['carnations'] + 1 == cigar_vars['blends'])
    
    # Clue 23: Eric is blends smoker
    s.add(name_vars['Eric'] == cigar_vars['blends'])
    
    # Clue 24: Volleyball lover uses iPhone 13
    s.add(sport_vars['volleyball'] == phone_vars['iphone 13'])
    
    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        solution = []
        for house in range(1, 7):
            row = [str(house)]
            # Find name for this house
            for name in names:
                if model.eval(name_vars[name]).as_long() == house:
                    row.append(name)
                    break
            # Find phone for this house
            for phone in phones:
                if model.eval(phone_vars[phone]).as_long() == house:
                    row.append(phone)
                    break
            # Find cigar for this house
            for cigar in cigars:
                if model.eval(cigar_vars[cigar]).as_long() == house:
                    row.append(cigar)
                    break
            # Find flower for this house
            for flower in flowers:
                if model.eval(flower_vars[flower]).as_long() == house:
                    row.append(flower)
                    break
            # Find color for this house
            for color in colors:
                if model.eval(color_vars[color]).as_long() == house:
                    row.append(color)
                    break
            # Find sport for this house
            for sport in sports:
                if model.eval(sport_vars[sport]).as_long() == house:
                    row.append(sport)
                    break
            solution.append(row)
        
        # Format as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"],
                "rows": solution
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    import json
    main()