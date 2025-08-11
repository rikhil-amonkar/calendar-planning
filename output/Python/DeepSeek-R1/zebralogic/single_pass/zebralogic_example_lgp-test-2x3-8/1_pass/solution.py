import json

def main():
    names = ['Arnold', 'Eric']
    birthdays = ['april', 'sept']
    mothers = ['Aniya', 'Holly']
    
    found = False
    solution_house1 = None
    solution_house2 = None
    
    for name1 in names:
        for bd1 in birthdays:
            for mother1 in mothers:
                name2 = next(n for n in names if n != name1)
                bd2 = next(b for b in birthdays if b != bd1)
                mother2 = next(m for m in mothers if m != mother1)
                
                eric_house = 1 if name1 == 'Eric' else 2
                holly_house = 1 if mother1 == 'Holly' else 2
                if eric_house >= holly_house:
                    continue
                    
                if bd1 != 'april':
                    continue
                
                solution_house1 = {'House': 1, 'Name': name1, 'Birthday Month': bd1, "Mother's Name": mother1}
                solution_house2 = {'House': 2, 'Name': name2, 'Birthday Month': bd2, "Mother's Name": mother2}
                found = True
                break
            if found:
                break
        if found:
            break
            
    if found:
        header = ['House', 'Name', 'Birthday Month', "Mother's Name"]
        row1 = [str(solution_house1['House']), solution_house1['Name'], solution_house1['Birthday Month'], solution_house1["Mother's Name"]]
        row2 = [str(solution_house2['House']), solution_house2['Name'], solution_house2['Birthday Month'], solution_house2["Mother's Name"]]
        solution = {
            "header": header,
            "rows": [row1, row2]
        }
        output = {"solution": solution}
    else:
        output = {"solution": {}}
        
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()