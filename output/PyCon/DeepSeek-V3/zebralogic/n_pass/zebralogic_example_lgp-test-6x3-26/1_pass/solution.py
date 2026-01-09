from constraint import Problem
import json

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold', 'Carol']
    heights = ['very tall', 'tall', 'super tall', 'average', 'very short', 'short']
    phones = ['oneplus 9', 'google pixel 6', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'xiaomi mi 11']
    
    problem.addVariables(["name"], names)
    problem.addVariables(["height"], heights)
    problem.addVariables(["phone"], phones)
    problem.addVariables(["house"], houses)
    
    problem.addConstraint(lambda n1, n2, n3, n4, n5, n6: 
                         len([n1, n2, n3, n4, n5, n6]) == len(set([n1, n2, n3, n4, n5, n6])),
                         ["name1", "name2", "name3", "name4", "name5", "name6"])
    problem.addConstraint(lambda h1, h2, h3, h4, h5, h6: 
                         len([h1, h2, h3, h4, h5, h6]) == len(set([h1, h2, h3, h4, h5, h6])),
                         ["height1", "height2", "height3", "height4", "height5", "height6"])
    problem.addConstraint(lambda p1, p2, p3, p4, p5, p6: 
                         len([p1, p2, p3, p4, p5, p6]) == len(set([p1, p2, p3, p4, p5, p6])),
                         ["phone1", "phone2", "phone3", "phone4", "phone5", "phone6"])
    
    # Clue 1: Bob is directly left of the person who is tall.
    problem.addConstraint(lambda b_house, tall_house: b_house + 1 == tall_house,
                         ["Bob_house", "tall_house"])
    
    # Clue 2: Peter is somewhere to the left of the person who uses an iPhone 13.
    problem.addConstraint(lambda p_house, iphone_house: p_house < iphone_house,
                         ["Peter_house", "iphone_house"])
    
    # Clue 3: The person who is very short is somewhere to the right of the person who uses a Google Pixel 6.
    problem.addConstraint(lambda gp_house, vs_house: gp_house < vs_house,
                         ["gp_house", "vs_house"])
    
    # Clue 4: Carol is the person who is very tall.
    problem.addConstraint(lambda carol_house, vt_house: carol_house == vt_house,
                         ["Carol_house", "vt_house"])
    
    # Clue 5: There is one house between the person who uses a Google Pixel 6 and the person who is short.
    problem.addConstraint(lambda gp_house, short_house: abs(gp_house - short_house) == 2,
                         ["gp_house", "short_house"])
    
    # Clue 6: The person who uses a Samsung Galaxy S21 is not in the first house.
    problem.addConstraint(lambda s21_house: s21_house != 1, ["s21_house"])
    
    # Clue 7: The person who uses a OnePlus 9 is directly left of the person who is short.
    problem.addConstraint(lambda op9_house, short_house: op9_house + 1 == short_house,
                         ["op9_house", "short_house"])
    
    # Clue 8: The person who is tall is Arnold.
    problem.addConstraint(lambda tall_house, arnold_house: tall_house == arnold_house,
                         ["tall_house", "Arnold_house"])
    
    # Clue 9: The person who is super tall is in the first house.
    problem.addConstraint(lambda st_house: st_house == 1, ["st_house"])
    
    # Clue 10: The person who uses a Xiaomi Mi 11 is Carol.
    problem.addConstraint(lambda xm_house, carol_house: xm_house == carol_house,
                         ["xm_house", "Carol_house"])
    
    # Clue 11: The person who uses a Google Pixel 6 is somewhere to the right of Eric.
    problem.addConstraint(lambda eric_house, gp_house: eric_house < gp_house,
                         ["Eric_house", "gp_house"])
    
    # Clue 12: The person who is short is in the sixth house.
    problem.addConstraint(lambda short_house: short_house == 6, ["short_house"])
    
    # Add variable assignments for each house
    for i in range(1, 7):
        problem.addConstraint(lambda name, house=i: name == f"name{house}", [f"name_house{i}"])
        problem.addConstraint(lambda height, house=i: height == f"height{house}", [f"height_house{i}"])
        problem.addConstraint(lambda phone, house=i: phone == f"phone{house}", [f"phone_house{i}"])
    
    # Add constraints for each clue variable
    for name in names:
        problem.addConstraint(lambda nh, n=name: nh == n, [f"{name}_house"])
    
    for height in heights:
        problem.addConstraint(lambda hh, h=height: hh == h, [f"{height.replace(' ', '_')}_house"])
    
    for phone in phones:
        problem.addConstraint(lambda ph, p=phone: ph == p, [f"{phone.replace(' ', '_').replace('-', '_')}_house"])
    
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Height", "PhoneModel"], "rows": []}}
    
    solution = solutions[0]
    
    result = {
        "solution": {
            "header": ["House", "Name", "Height", "PhoneModel"],
            "rows": []
        }
    }
    
    for house in range(1, 7):
        name = solution[f"name_house{house}"]
        height = solution[f"height_house{house}"]
        phone = solution[f"phone_house{house}"]
        result["solution"]["rows"].append([str(house), name, height, phone])
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))