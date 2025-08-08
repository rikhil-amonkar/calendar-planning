from z3 import *
import json

def main():
    City = Datatype('City')
    City.declare('Amsterdam')
    City.declare('Vienna')
    City.declare('Santorini')
    City.declare('Lyon')
    City = City.create()
    
    edges = [
        (City.Vienna, City.Lyon),
        (City.Vienna, City.Santorini),
        (City.Vienna, City.Amsterdam),
        (City.Amsterdam, City.Santorini),
        (City.Lyon, City.Amsterdam)
    ]
    direct_pairs = []
    for (a, b) in edges:
        direct_pairs.append((a, b))
        direct_pairs.append((b, a))
    
    s = Solver()
    
    b = [None]
    e = [None]
    for i in range(1, 15):
        b.append(Const(f'b_{i}', City))
        e.append(Const(f'e_{i}', City))
    
    for i in range(2, 15):
        s.add(b[i] == e[i-1])
    
    for i in range(1, 15):
        constraint = Or([And(b[i] == c1, e[i] == c2) for (c1, c2) in direct_pairs])
        s.add(If(b[i] != e[i], constraint, True))
    
    total_days = { 
        City.Amsterdam: 0,
        City.Vienna: 0,
        City.Santorini: 0,
        City.Lyon: 0
    }
    for city in total_days.keys():
        for i in range(1, 15):
            total_days[city] += If(Or(b[i] == city, e[i] == city), 1, 0)
    
    s.add(total_days[City.Amsterdam] == 3)
    s.add(total_days[City.Vienna] == 7)
    s.add(total_days[City.Santorini] == 4)
    s.add(total_days[City.Lyon] == 3)
    
    workshop_days = []
    for i in [9, 10, 11]:
        workshop_days.append(Or(b[i] == City.Amsterdam, e[i] == City.Amsterdam))
    s.add(Or(workshop_days))
    
    wedding_days = []
    for i in [7, 8, 9]:
        wedding_days.append(Or(b[i] == City.Lyon, e[i] == City.Lyon))
    s.add(Or(wedding_days))
    
    travel_days = [If(b[i] != e[i], 1, 0) for i in range(1, 15)]
    s.add(sum(travel_days) == 3)
    
    if s.check() == sat:
        m = s.model()
        day_reps = []
        for i in range(1, 15):
            b_val = m[b[i]]
            e_val = m[e[i]]
            if b_val == e_val:
                if b_val == City.Amsterdam:
                    rep = "Amsterdam"
                elif b_val == City.Vienna:
                    rep = "Vienna"
                elif b_val == City.Santorini:
                    rep = "Santorini"
                elif b_val == City.Lyon:
                    rep = "Lyon"
                else:
                    rep = "Unknown"
            else:
                if b_val == City.Amsterdam:
                    b_str = "Amsterdam"
                elif b_val == City.Vienna:
                    b_str = "Vienna"
                elif b_val == City.Santorini:
                    b_str = "Santorini"
                elif b_val == City.Lyon:
                    b_str = "Lyon"
                else:
                    b_str = "Unknown"
                
                if e_val == City.Amsterdam:
                    e_str = "Amsterdam"
                elif e_val == City.Vienna:
                    e_str = "Vienna"
                elif e_val == City.Santorini:
                    e_str = "Santorini"
                elif e_val == City.Lyon:
                    e_str = "Lyon"
                else:
                    e_str = "Unknown"
                rep = f"{b_str}/{e_str}"
            day_reps.append(rep)
        
        itinerary = []
        current_start = 1
        current_rep = day_reps[0]
        
        for day in range(1, 14):
            if day_reps[day] != current_rep:
                if current_start == day:
                    itinerary.append({'day_range': f'Day {current_start}', 'place': current_rep})
                else:
                    itinerary.append({'day_range': f'Day {current_start}-{day}', 'place': current_rep})
                current_start = day + 1
                current_rep = day_reps[day]
        
        if current_start == 14:
            itinerary.append({'day_range': 'Day 14', 'place': day_reps[13]})
        else:
            itinerary.append({'day_range': f'Day {current_start}-14', 'place': day_reps[13]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()