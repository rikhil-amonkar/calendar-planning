import json

def main():
    names = ["Arnold", "Eric"]
    birthdays = ["april", "sept"]
    mothers = ["Aniya", "Holly"]
    
    found = False
    solution_rows = None
    
    for n1 in names:
        n2 = "Eric" if n1 == "Arnold" else "Arnold"
        
        for b1 in birthdays:
            if b1 != 'april':
                continue
            b2 = "sept"  # Since birthdays are unique and b1 is 'april'
            
            for m1 in mothers:
                m2 = "Aniya" if m1 == "Holly" else "Holly"
                
                eric_house = 1 if n1 == 'Eric' else 2
                holly_house = 1 if m1 == 'Holly' else 2
                
                if eric_house < holly_house:
                    solution_rows = [
                        ["1", n1, b1, m1],
                        ["2", n2, b2, m2]
                    ]
                    found = True
                    break
            if found:
                break
        if found:
            break
            
    if solution_rows is None:
        solution_rows = []
        
    result = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother"],
            "rows": solution_rows
        }
    }
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()