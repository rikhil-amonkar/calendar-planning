from constraint import Problem
import json

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold', 'Carol']
    heights = ['very tall', 'tall', 'super tall', 'average', 'very short', 'short']
    phones = ['oneplus 9', 'google pixel 6', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'xiaomi mi 11']
    
    # Define variables for each house
    for i in range(1, 7):
        problem.addVariable(f"name{i}", names)
        problem.addVariable(f"height{i}", heights)
        problem.addVariable(f"phone{i}", phones)
    
    # All different constraints
    problem.addConstraint(lambda n1, n2, n3, n4, n5, n6: 
                         len([n1, n2, n3, n4, n5, n6]) == len(set([n1, n2, n3, n4, n5, n6])),
                         ["name1", "name2", "name3", "name4", "name5", "name6"])
    problem.addConstraint(lambda h1, h2, h3, h4, h5, h6: 
                         len([h1, h2, h3, h4, h5, h6]) == len(set([h1, h2, h3, h4, h5, h6])),
                         ["height1", "height2", "height3", "height4", "height5", "height6"])
    problem.addConstraint(lambda p1, p2, p3, p4, p5, p6: 
                         len([p1, p2, p3, p4, p5, p6]) == len(set([p1, p2, p3, p4, p5, p6])),
                         ["phone1", "phone2", "phone3", "phone4", "phone5", "phone6"])
    
    # Define helper variables for clues
    for name in names:
        problem.addVariable(f"{name}_house", houses)
    for height in heights:
        problem.addVariable(f"{height.replace(' ', '_')}_house", houses)
    for phone in phones:
        problem.addVariable(f"{phone.replace(' ', '_').replace('-', '_')}_house", houses)
    
    # Link helper variables to actual assignments
    for i in range(1, 7):
        problem.addConstraint(lambda name, house=i, n_var=f"name{i}": name == house,
                             [f"name_house{i}", n_var])
        for name in names:
            problem.addConstraint(lambda nh, house=i, n=name, n_var=f"name{i}": (nh == house) == (n_var == n),
                                 [f"{name}_house", n_var])
        
        problem.addConstraint(lambda height, house=i, h_var=f"height{i}": height == house,
                             [f"height_house{i}", h_var])
        for height in heights:
            problem.addConstraint(lambda hh, house=i, h=height, h_var=f"height{i}": (hh == house) == (h_var == h),
                                 [f"{height.replace(' ', '_')}_house", h_var])
        
        problem.addConstraint(lambda phone, house=i, p_var=f"phone{i}": phone == house,
                             [f"phone_house{i}", p_var])
        for phone in phones:
            problem.addConstraint(lambda ph, house=i, p=phone, p_var=f"phone{i}": (ph == house) == (p_var == p),
                                 [f"{phone.replace(' ', '_').replace('-', '_')}_house", p_var])
    
    # Clue 1: Bob is directly left of the person who is tall.
    problem.addConstraint(lambda b_house, tall_house: b_house + 1 == tall_house,
                         ["Bob_house", "tall_house"])
    
    # Clue 2: Peter is somewhere to the left of the person who uses an iPhone 13.
    problem.addConstraint(lambda p_house, iphone_house: p_house < iphone_house,
                         ["Peter_house", "iphone_13_house"])
    
    # Clue 3: The person who is very short is somewhere to the right of the person who uses a Google Pixel 6.
    problem.addConstraint(lambda gp_house, vs_house: gp_house < vs_house,
                         ["google_pixel_6_house", "very_short_house"])
    
    # Clue 4: Carol is the person who is very tall.
    problem.addConstraint(lambda carol_house, vt_house: carol_house == vt_house,
                         ["Carol_house", "very_tall_house"])
    
    # Clue 5: There is one house between the person who uses a Google Pixel 6 and the person who is short.
    problem.addConstraint(lambda gp_house, short_house: abs(gp_house - short_house) == 2,
                         ["google_pixel_6_house", "short_house"])
    
    # Clue 6: The person who uses a Samsung Galaxy S21 is not in the first house.
    problem.addConstraint(lambda s21_house: s21_house != 1, ["samsung_galaxy_s21_house"])
    
    # Clue 7: The person who uses a OnePlus 9 is directly left of the person who is short.
    problem.addConstraint(lambda op9_house, short_house: op9_house + 1 == short_house,
                         ["oneplus_9_house", "short_house"])
    
    # Clue 8: The person who is tall is Arnold.
    problem.addConstraint(lambda tall_house, arnold_house: tall_house == arnold_house,
                         ["tall_house", "Arnold_house"])
    
    # Clue 9: The person who is super tall is in the first house.
    problem.addConstraint(lambda st_house: st_house == 1, ["super_tall_house"])
    
    # Clue 10: The person who uses a Xiaomi Mi 11 is Carol.
    problem.addConstraint(lambda xm_house, carol_house: xm_house == carol_house,
                         ["xiaomi_mi_11_house", "Carol_house"])
    
    # Clue 11: The person who uses a Google Pixel 6 is somewhere to the right of Eric.
    problem.addConstraint(lambda eric_house, gp_house: eric_house < gp_house,
                         ["Eric_house", "google_pixel_6_house"])
    
    # Clue 12: The person who is short is in the sixth house.
    problem.addConstraint(lambda short_house: short_house == 6, ["short_house"])
    
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
        name = solution[f"name{house}"]
        height = solution[f"height{house}"]
        phone = solution[f"phone{house}"]
        result["solution"]["rows"].append([str(house), name, height, phone])
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))