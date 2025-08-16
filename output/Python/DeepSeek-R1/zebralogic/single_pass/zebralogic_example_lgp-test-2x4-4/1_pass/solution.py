import json

def main():
    names = ['Eric', 'Arnold']
    house_styles = ['victorian', 'colonial']
    heights = ['very short', 'short']
    educations = ['associate', 'high school']
    
    solution_rows = None
    
    for name1 in names:
        for style1 in house_styles:
            if style1 != 'victorian':
                continue
            for height1 in heights:
                for education1 in educations:
                    name2 = (set(names) - {name1}).pop()
                    style2 = (set(house_styles) - {style1}).pop()
                    height2 = (set(heights) - {height1}).pop()
                    education2 = (set(educations) - {education1}).pop()
                    
                    if height1 == 'short' and name2 == 'Eric' and education1 == 'associate':
                        solution_rows = [
                            ['1', name1, style1, height1, education1],
                            ['2', name2, style2, height2, education2]
                        ]
                        break
                if solution_rows:
                    break
            if solution_rows:
                break
        if solution_rows:
            break
            
    if solution_rows is None:
        solution_rows = []
        
    output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Height", "Education"],
            "rows": solution_rows
        }
    }
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()