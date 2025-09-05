from z3 import *
import json

def main():
    s = Solver()
    
    names = ['Arnold', 'Carol', 'Peter', 'Eric', 'Bob', 'Alice']
    house_styles = ['ranch', 'colonial', 'modern', 'craftsman', 'mediterranean', 'victorian']
    foods = ['pizza', 'stew', 'spaghetti', 'grilled cheese', 'stir fry', 'soup']
    vacations = ['cultural', 'cruise', 'mountain', 'camping', 'city', 'beach']
    heights = ['average', 'very tall', 'very short', 'short', 'tall', 'super tall']
    cigars = ['yellow monster', 'prince', 'dunhill', 'pall mall', 'blue master', 'blends']
    
    name_house = [Int('name_%s' % n) for n in names]
    style_house = [Int('style_%s' % hs) for hs in house_styles]
    food_house = [Int('food_%s' % f) for f in foods]
    vacation_house = [Int('vacation_%s' % v) for v in vacations]
    height_house = [Int('height_%s' % h) for h in heights]
    cigar_house = [Int('cigar_%s' % c) for c in cigars]
    
    for lst in [name_house, style_house, food_house, vacation_house, height_house, cigar_house]:
        s.add(Distinct(lst))
        for var in lst:
            s.add(var >= 1, var <= 6)
    
    s.add(name_house[names.index('Alice')] == 5)
    s.add(food_house[foods.index('stir fry')] == style_house[house_styles.index('colonial')])
    s.add(name_house[names.index('Alice')] == food_house[foods.index('spaghetti')])
    s.add(name_house[names.index('Arnold')] == food_house[foods.index('stew')])
    
    avg_height = height_house[heights.index('average')]
    peter_house = name_house[names.index('Peter')]
    s.add(Or(avg_height == peter_house - 2, avg_height == peter_house + 2))
    
    s.add(style_house[house_styles.index('craftsman')] != 3)
    s.add(height_house[heights.index('average')] == food_house[foods.index('stir fry')])
    s.add(vacation_house[vacations.index('beach')] == style_house[house_styles.index('ranch')])
    s.add(name_house[names.index('Eric')] == 4)
    
    colonial_house = style_house[house_styles.index('colonial')]
    camping_house = vacation_house[vacations.index('camping')]
    s.add(Or(colonial_house == camping_house - 2, colonial_house == camping_house + 2))
    
    s.add(vacation_house[vacations.index('mountain')] == cigar_house[cigars.index('yellow monster')])
    s.add(vacation_house[vacations.index('mountain')] == height_house[heights.index('very tall')])
    
    mountain_house = vacation_house[vacations.index('mountain')]
    dunhill_house = cigar_house[cigars.index('dunhill')]
    s.add(Or(mountain_house == dunhill_house - 1, mountain_house == dunhill_house + 1))
    
    s.add(food_house[foods.index('spaghetti')] == style_house[house_styles.index('victorian')])
    s.add(height_house[heights.index('tall')] == vacation_house[vacations.index('beach')])
    s.add(height_house[heights.index('tall')] < style_house[house_styles.index('victorian')])
    
    stir_fry_house = food_house[foods.index('stir fry')]
    bob_house = name_house[names.index('Bob')]
    s.add(stir_fry_house == bob_house - 1)
    
    s.add(style_house[house_styles.index('modern')] < name_house[names.index('Alice')])
    s.add(style_house[house_styles.index('craftsman')] < height_house[heights.index('short')])
    s.add(food_house[foods.index('stir fry')] < cigar_house[cigars.index('prince')])
    
    grilled_cheese_house = food_house[foods.index('grilled cheese')]
    super_tall_house = height_house[heights.index('super tall')]
    s.add(Or(grilled_cheese_house == super_tall_house - 3, grilled_cheese_house == super_tall_house + 3))
    
    s.add(style_house[house_styles.index('ranch')] == cigar_house[cigars.index('blue master')])
    
    blends_house = cigar_house[cigars.index('blends')]
    blue_master_house = cigar_house[cigars.index('blue master')]
    s.add(blends_house == blue_master_house - 1)
    
    s.add(vacation_house[vacations.index('cultural')] == food_house[foods.index('pizza')])
    s.add(food_house[foods.index('pizza')] < vacation_house[vacations.index('cruise')])
    
    if s.check() == sat:
        m = s.model()
        result = []
        for house_num in range(1, 7):
            row = [str(house_num)]
            for i in range(len(names)):
                if m.eval(name_house[i]).as_long() == house_num:
                    row.append(names[i])
                    break
            for i in range(len(house_styles)):
                if m.eval(style_house[i]).as_long() == house_num:
                    row.append(house_styles[i])
                    break
            for i in range(len(foods)):
                if m.eval(food_house[i]).as_long() == house_num:
                    row.append(foods[i])
                    break
            for i in range(len(vacations)):
                if m.eval(vacation_house[i]).as_long() == house_num:
                    row.append(vacations[i])
                    break
            for i in range(len(heights)):
                if m.eval(height_house[i]).as_long() == house_num:
                    row.append(heights[i])
                    break
            for i in range(len(cigars)):
                if m.eval(cigar_house[i]).as_long() == house_num:
                    row.append(cigars[i])
                    break
            result.append(row)
        
        output = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
                "rows": result
            }
        }
        print(json.dumps(output))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()