from z3 import *
import json

def main():
    # Define the enums with the exact problem strings
    Name, (Arnold, Eric, Alice, Bob, Peter) = EnumSort('Name', ['Arnold','Eric','Alice','Bob','Peter'])
    Vacation, (mountain, city, cruise, beach, camping) = EnumSort('Vacation', ['mountain','city','cruise','beach','camping'])
    Education, (doctorate, high_school, bachelor, associate, master) = EnumSort('Education', ['doctorate','high school','bachelor','associate','master'])
    Color, (blue, red, white, yellow, green) = EnumSort('Color', ['blue','red','white','yellow','green'])
    PhoneModel, (google_pixel_6, iphone_13, oneplus_9, huawei_p50, samsung_galaxy_s21) = EnumSort('PhoneModel', 
            ['google pixel 6','iphone 13','oneplus 9','huawei p50','samsung galaxy s21'])
    Food, (grilled_cheese, stir_fry, pizza, spaghetti, stew) = EnumSort('Food', 
            ['grilled cheese','stir fry','pizza','spaghetti','stew'])

    num_houses = 5
    houses = list(range(num_houses))  # [0,1,2,3,4] representing house1 to house5

    # Create the attributes for each house
    names = [Const('name_%d' % i, Name) for i in houses]
    vacations = [Const('vacation_%d' % i, Vacation) for i in houses]
    educations = [Const('education_%d' % i, Education) for i in houses]
    colors = [Const('color_%d' % i, Color) for i in houses]
    phones = [Const('phone_%d' % i, PhoneModel) for i in houses]
    foods = [Const('food_%d' % i, Food) for i in houses]

    s = Solver()

    # All attributes must be distinct for each house
    s.add(Distinct(names))
    s.add(Distinct(vacations))
    s.add(Distinct(educations))
    s.add(Distinct(colors))
    s.add(Distinct(phones))
    s.add(Distinct(foods))

    # Clue 1: The person who loves the stew is not in the first house.
    s.add(foods[0] != stew)

    # Clue 2: There are two houses between the person who loves stir fry and the person with an associate's degree.
    s.add(Or(
        And(foods[0] == stir_fry, educations[3] == associate),
        And(foods[3] == stir_fry, educations[0] == associate),
        And(foods[1] == stir_fry, educations[4] == associate),
        And(foods[4] == stir_fry, educations[1] == associate)
    ))

    # Clue 3: The person who enjoys mountain retreats is the person with a bachelor's degree.
    # Clue 8: The person who loves stir fry is the person with a bachelor's degree.
    for i in houses:
        s.add( (vacations[i] == mountain) == (educations[i] == bachelor) )
        s.add( (educations[i] == bachelor) == (foods[i] == stir_fry) )

    # Clue 4: The person with a doctorate is somewhere to the right of Bob.
    # Clue 7: The person with a doctorate is in the third house -> house3 (index2) has doctorate.
    # So Bob must be in house1 (index0) or house2 (index1)
    bob_house = Int('bob_house')
    s.add(Or([And(bob_house == i+1, names[i] == Bob) for i in houses]))
    s.add(bob_house < 3)  # Bob is left of house3 (so house1 or house2)

    # Clue 5: The person who uses a Samsung Galaxy S21 is in the third house.
    s.add(phones[2] == samsung_galaxy_s21)

    # Clue 6: Eric is the person with a doctorate.
    # Clue 7: The person with a doctorate is in the third house -> so house3: Eric and doctorate.
    s.add(names[2] == Eric)
    s.add(educations[2] == doctorate)

    # Clue 9: The person with a doctorate is the person who is a pizza lover -> house3: pizza.
    s.add(foods[2] == pizza)

    # Clue 10: The person whose favorite color is green is somewhere to the right of Peter.
    peter_house = Int('peter_house')
    green_house = Int('green_house')
    s.add(Or([And(peter_house == i+1, names[i] == Peter) for i in houses]))
    s.add(Or([And(green_house == i+1, colors[i] == green) for i in houses]))
    s.add(green_house > peter_house)

    # Clue 11: The person who enjoys camping trips is the person who uses an iPhone 13.
    for i in houses:
        s.add( (vacations[i] == camping) == (phones[i] == iphone_13) )

    # Clue 12: The person who likes going on cruises is Alice.
    for i in houses:
        s.add( (names[i] == Alice) == (vacations[i] == cruise) )

    # Clue 13: There is one house between the person with a high school diploma and the person who uses a Samsung Galaxy S21.
    # Samsung is in house3 (index2). So high school must be in house1 (index0) or house5 (index4).
    high_school_house = Int('high_school_house')
    s.add(Or([And(high_school_house == i+1, educations[i] == high_school) for i in houses]))
    s.add(Or(high_school_house == 1, high_school_house == 5))

    # Clue 14: The person who uses a Google Pixel 6 is Arnold.
    for i in houses:
        s.add( (names[i] == Arnold) == (phones[i] == google_pixel_6) )

    # Clue 15: The person who uses a OnePlus 9 is somewhere to the right of the person who uses a Huawei P50.
    oneplus_house = Int('oneplus_house')
    huawei_house = Int('huawei_house')
    s.add(Or([And(oneplus_house == i+1, phones[i] == oneplus_9) for i in houses]))
    s.add(Or([And(huawei_house == i+1, phones[i] == huawei_p50) for i in houses]))
    s.add(oneplus_house > huawei_house)

    # Clue 16: Arnold is the person who loves eating grilled cheese.
    for i in houses:
        s.add( (names[i] == Arnold) == (foods[i] == grilled_cheese) )

    # Clue 17: The person who loves eating grilled cheese is not in the fourth house (house4, index3).
    s.add(foods[3] != grilled_cheese)

    # Clue 18: There are two houses between the person with a bachelor's degree and the person whose favorite color is red.
    bachelor_house = Int('bachelor_house')
    red_house = Int('red_house')
    s.add(Or([And(bachelor_house == i+1, educations[i] == bachelor) for i in houses]))
    s.add(Or([And(red_house == i+1, colors[i] == red) for i in houses]))
    s.add(Or( 
        bachelor_house - red_house == 3,
        red_house - bachelor_house == 3
    ))

    # Clue 19: The person who loves beach vacations is somewhere to the right of the person who prefers city breaks.
    beach_house = Int('beach_house')
    city_house = Int('city_house')
    s.add(Or([And(beach_house == i+1, vacations[i] == beach) for i in houses]))
    s.add(Or([And(city_house == i+1, vacations[i] == city) for i in houses]))
    s.add(beach_house > city_house)

    # Clue 20: The person whose favorite color is green is not in the second house (house2, index1).
    s.add(colors[1] != green)

    # Clue 21: The person who loves blue is somewhere to the right of Peter.
    blue_house = Int('blue_house')
    s.add(Or([And(blue_house == i+1, colors[i] == blue) for i in houses]))
    s.add(blue_house > peter_house)

    # Clue 22: There is one house between the person who enjoys camping trips and the person who loves yellow.
    camping_house = Int('camping_house')
    yellow_house = Int('yellow_house')
    s.add(Or([And(camping_house == i+1, vacations[i] == camping) for i in houses]))
    s.add(Or([And(yellow_house == i+1, colors[i] == yellow) for i in houses]))
    s.add(Or( 
        camping_house - yellow_house == 2,
        yellow_house - camping_house == 2
    ))

    if s.check() == sat:
        m = s.model()
        rows = []
        for i in houses:
            house_num = i + 1
            name_val = m.eval(names[i])
            vacation_val = m.eval(vacations[i])
            education_val = m.eval(educations[i])
            color_val = m.eval(colors[i])
            phone_val = m.eval(phones[i])
            food_val = m.eval(foods[i])
            row = [str(house_num),
                   str(name_val),
                   str(vacation_val),
                   str(education_val),
                   str(color_val),
                   str(phone_val),
                   str(food_val)]
            rows.append(row)
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()