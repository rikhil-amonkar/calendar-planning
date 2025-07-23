import z3
import json

def main():
    # Define the City type
    City = z3.Datatype('City')
    City.declare('Madrid')
    City.declare('Dublin')
    City.declare('Tallinn')
    City = City.create()
    
    # Create variables for 7 days: s0 to s6, e0 to e6
    s = [z3.Const('s_%d' % i, City) for i in range(7)]
    e = [z3.Const('e_%d' % i, City) for i in range(7)]
    
    solver = z3.Solver()
    
    # Continuity constraint: the end of day i is the start of day i+1
    for i in range(6):
        solver.add(e[i] == s[i+1])
    
    # Flight constraints: either no travel or a direct flight
    for i in range(7):
        no_travel = s[i] == e[i]
        travel_MD = z3.And(s[i] == City.Madrid, e[i] == City.Dublin)
        travel_DM = z3.And(s[i] == City.Dublin, e[i] == City.Madrid)
        travel_DT = z3.And(s[i] == City.Dublin, e[i] == City.Tallinn)
        travel_TD = z3.And(s[i] == City.Tallinn, e[i] == City.Dublin)
        solver.add(z3.Or(no_travel, travel_MD, travel_DM, travel_DT, travel_TD))
    
    # Count constraints for each city
    count_M = 0
    count_D = 0
    count_T = 0
    for i in range(7):
        in_M = z3.Or(s[i] == City.Madrid, e[i] == City.Madrid)
        in_D = z3.Or(s[i] == City.Dublin, e[i] == City.Dublin)
        in_T = z3.Or(s[i] == City.Tallinn, e[i] == City.Tallinn)
        count_M += z3.If(in_M, 1, 0)
        count_D += z3.If(in_D, 1, 0)
        count_T += z3.If(in_T, 1, 0)
    solver.add(count_M == 4, count_D == 3, count_T == 2)
    
    # Workshop constraints: must be in Tallinn on days 6 and 7
    solver.add(z3.Or(s[5] == City.Tallinn, e[5] == City.Tallinn))
    solver.add(z3.Or(s[6] == City.Tallinn, e[6] == City.Tallinn))
    
    # Solve the problem
    if solver.check() == z3.sat:
        m = solver.model()
        itinerary_list = []
        names = ["Madrid", "Dublin", "Tallinn"]
        
        for i in range(7):
            s_val = m[s[i]]
            e_val = m[e[i]]
            s_val_int = s_val.as_long()
            e_val_int = e_val.as_long()
            s_name = names[s_val_int]
            e_name = names[e_val_int]
            
            itinerary_list.append({"day": i+1, "place": s_name})
            if s_val_int != e_val_int:
                itinerary_list.append({"day": i+1, "place": e_name})
                
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()