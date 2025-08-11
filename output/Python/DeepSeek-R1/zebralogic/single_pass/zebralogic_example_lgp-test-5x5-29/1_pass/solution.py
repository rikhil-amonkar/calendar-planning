import itertools
import json

def main():
    houses = [0,1,2,3,4]
    # We'll iterate over beach positions: 0,1,2
    for beach in [0,1,2]:
        arnold_house = beach + 1
        for cruise in range(beach+1, 4): 
            for eric_house in [x for x in [0,1,3] if x != beach and x != cruise]:
                vac = [None] * 5
                vac[4] = 'mountain'
                vac[beach] = 'beach'
                vac[cruise] = 'cruise'
                vac[eric_house] = 'camping'
                remaining_vac_houses = [x for x in [0,1,2,3] if x not in [beach, cruise, eric_house]]
                if len(remaining_vac_houses) != 1:
                    continue
                city_house = remaining_vac_houses[0]
                vac[city_house] = 'city'
                
                if beach >= city_house:
                    continue
                    
                edu = [None] * 5
                edu[2] = 'bachelor'
                edu[eric_house] = 'master'
                edu[cruise] = 'associate'
                
                if cruise + 1 >= 5:
                    continue
                
                remaining_edu_houses = [x for x in range(5) if edu[x] is None]
                remaining_edu = ['doctorate', 'high school']
                if len(remaining_edu_houses) != 2:
                    continue
                    
                for perm_edu in itertools.permutations(remaining_edu):
                    edu[remaining_edu_houses[0]] = perm_edu[0]
                    edu[remaining_edu_houses[1]] = perm_edu[1]
                    
                    names = [None] * 5
                    names[arnold_house] = 'Arnold'
                    names[eric_house] = 'Eric'
                    
                    remaining_name_houses = [x for x in range(5) if names[x] is None]
                    remaining_names = ['Alice', 'Bob', 'Peter']
                    for perm_name in itertools.permutations(remaining_names):
                        for idx, house in enumerate(remaining_name_houses):
                            names[house] = perm_name[idx]
                            
                        if names[0] == 'Peter':
                            continue
                        if names[3] == 'Bob':
                            continue
                        if names[0] == 'Bob':
                            continue
                            
                        bob_index = names.index('Bob')
                        found_doctorate = False
                        for i in range(bob_index):
                            if edu[i] == 'doctorate':
                                found_doctorate = True
                                break
                        if not found_doctorate:
                            continue
                            
                        nats = [None] * 5
                        nats[eric_house] = 'brit'
                        alice_index = names.index('Alice')
                        nats[alice_index] = 'german'
                        peter_index = names.index('Peter')
                        nats[peter_index] = 'swede'
                        
                        bachelor_index = 2
                        norwegian_options = [1, 3]
                        remaining_nat_houses = [x for x in range(5) if nats[x] is None]
                        remaining_nats = ['norwegian', 'dane']
                        if len(remaining_nat_houses) != 2:
                            continue
                            
                        valid_nat = False
                        for perm_nat in itertools.permutations(remaining_nats):
                            nats[remaining_nat_houses[0]] = perm_nat[0]
                            nats[remaining_nat_houses[1]] = perm_nat[1]
                            if 'norwegian' in nats:
                                norwegian_index = nats.index('norwegian')
                                if norwegian_index in norwegian_options:
                                    valid_nat = True
                                    break
                        if not valid_nat:
                            continue
                            
                        occ = [None] * 5
                        occ[cruise] = 'lawyer'
                        occ[peter_index] = 'artist'
                        occ[cruise+1] = 'engineer'
                        
                        dane_index = nats.index('dane')
                        remaining_occ_houses = [x for x in range(5) if occ[x] is None]
                        remaining_occ = ['doctor', 'teacher']
                        if len(remaining_occ_houses) != 2:
                            continue
                            
                        for perm_occ in itertools.permutations(remaining_occ):
                            occ[remaining_occ_houses[0]] = perm_occ[0]
                            occ[remaining_occ_houses[1]] = perm_occ[1]
                            
                            if 'doctor' in occ:
                                doctor_index = occ.index('doctor')
                                if doctor_index < dane_index:
                                    header = ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"]
                                    rows = []
                                    for i in range(5):
                                        row = [str(i+1), names[i], nats[i], vac[i], edu[i], occ[i]]
                                        rows.append(row)
                                    result = {
                                        "solution": {
                                            "header": header,
                                            "rows": rows
                                        }
                                    }
                                    print(json.dumps(result))
                                    return
                                    
    # If no solution found
    print(json.dumps({"solution": {}}))

if __name__ == '__main__':
    main()