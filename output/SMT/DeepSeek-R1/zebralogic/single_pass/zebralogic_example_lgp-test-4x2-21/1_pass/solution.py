from z3 import *
import json

def main():
    # Define variables for names and styles of each house
    name1, name2, name3, name4 = Ints('name1 name2 name3 name4')
    style1, style2, style3, style4 = Ints('style1 style2 style3 style4')
    
    s = Solver()
    
    # Fixed house2: Alice in craftsman
    s.add(name2 == 2)  # Alice is 2
    s.add(style2 == 0) # craftsman is 0
    
    # All names are distinct and in 0-3 (Eric=0, Arnold=1, Alice=2, Peter=3)
    s.add(Distinct(name1, name2, name3, name4))
    s.add(name1 >= 0, name1 <= 3)
    s.add(name2 >= 0, name2 <= 3)
    s.add(name3 >= 0, name3 <= 3)
    s.add(name4 >= 0, name4 <= 3)
    
    # All styles distinct and in 0-3 (craftsman=0, colonial=1, ranch=2, victorian=3)
    s.add(Distinct(style1, style2, style3, style4))
    s.add(style1 >= 0, style1 <= 3)
    s.add(style2 >= 0, style2 <= 3)
    s.add(style3 >= 0, style3 <= 3)
    s.add(style4 >= 0, style4 <= 3)
    
    # Clue 2: Victorian house (3) directly left of Peter (3)
    s.add(Or(
        And(style1 == 3, name2 == 3),
        And(style2 == 3, name3 == 3),
        And(style3 == 3, name4 == 3)
    ))
    
    # Clue 3: Peter (3) is right of ranch (2)
    ranch_house = If(style1 == 2, 1, If(style2 == 2, 2, If(style3 == 2, 3, 4)))
    peter_house = If(name1 == 3, 1, If(name2 == 3, 2, If(name3 == 3, 3, 4)))
    s.add(ranch_house < peter_house)
    
    # Clue 4: Arnold (1) is right of craftsman (0) which is house2 (index2)
    arnold_house = If(name1 == 1, 1, If(name2 == 1, 2, If(name3 == 1, 3, 4)))
    s.add(arnold_house > 2)
    
    if s.check() == sat:
        m = s.model()
        name_map = {0: "Eric", 1: "Arnold", 2: "Alice", 3: "Peter"}
        style_map = {0: "craftsman", 1: "colonial", 2: "ranch", 3: "victorian"}
        
        names = [name1, name2, name3, name4]
        styles = [style1, style2, style3, style4]
        
        rows = []
        for i in range(4):
            house_num = i + 1
            n_val = m.evaluate(names[i]).as_long()
            s_val = m.evaluate(styles[i]).as_long()
            rows.append([str(house_num), name_map[n_val], style_map[s_val]])
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": rows
            }
        }
        
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()