import json

def main():
    names_options = ['Arnold', 'Eric', 'Bob', 'Peter']
    smoothies_options = ['lime', 'desert', 'cherry']
    nationalities_options = ['german', 'dane', 'brit']
    
    solution_found = False
    sol_names = None
    sol_smoothies = None
    sol_nationalities = None

    for n0 in names_options:
        if n0 == 'Peter':
            continue
        names1 = [n for n in names_options if n != n0]
        for n1 in names1:
            names2 = [n for n in names1 if n != n1]
            for n3 in names2:
                names3 = [n for n in names2 if n != n3]
                if len(names3) != 1:
                    continue
                n4 = names3[0]
                names = [n0, n1, 'Alice', n3, n4]
                
                for s0 in smoothies_options:
                    smoothies1 = [s for s in smoothies_options if s != s0]
                    for s3 in smoothies1:
                        smoothies2 = [s for s in smoothies1 if s != s3]
                        if len(smoothies2) != 1:
                            continue
                        s4 = smoothies2[0]
                        if s4 == 'desert':
                            continue
                        smoothies = [s0, 'dragonfruit', 'watermelon', s3, s4]
                        
                        for nat1 in nationalities_options:
                            nats1 = [nat for nat in nationalities_options if nat != nat1]
                            for nat3 in nats1:
                                nats2 = [nat for nat in nats1 if nat != nat3]
                                if len(nats2) != 1:
                                    continue
                                nat4 = nats2[0]
                                nationalities = ['swede', nat1, 'norwegian', nat3, nat4]
                                
                                if 'Eric' not in names:
                                    continue
                                eric_index = names.index('Eric')
                                if eric_index <= 1:
                                    continue
                                
                                if 'dane' not in nationalities or 'brit' not in nationalities:
                                    continue
                                dane_index = nationalities.index('dane')
                                brit_index = nationalities.index('brit')
                                if abs(dane_index - brit_index) != 1:
                                    continue
                                
                                if 'lime' not in smoothies:
                                    continue
                                lime_index = smoothies.index('lime')
                                if abs(lime_index - dane_index) != 3:
                                    continue
                                
                                if 'Bob' not in names:
                                    continue
                                bob_index = names.index('Bob')
                                if nationalities[bob_index] != 'dane':
                                    continue
                                
                                sol_names = names
                                sol_smoothies = smoothies
                                sol_nationalities = nationalities
                                solution_found = True
                                break
                            if solution_found:
                                break
                        if solution_found:
                            break
                    if solution_found:
                        break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break
    
    if solution_found:
        rows = []
        for i in range(5):
            house_num = str(i+1)
            row = [house_num, sol_names[i], sol_smoothies[i], sol_nationalities[i]]
            rows.append(row)
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Nationality"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict))
    else:
        error_dict = {"error": "No solution found"}
        print(json.dumps(error_dict))

if __name__ == '__main__':
    main()