import z3
import json

def main():
    solver = z3.Solver()
    num_days = 16
    days = list(range(num_days))
    cities = ["Bucharest", "Lyon", "Porto"]
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Presence variables: presence[day][city] = True if traveler is in city on day
    presence = [[z3.Bool(f"d{day}_{city}") for city in cities] for day in days]
    
    # Initial constraint: Day 0 only in Bucharest
    solver.add(presence[0][0] == True)
    solver.add(presence[0][1] == False)
    solver.add(presence[0][2] == False)
    
    # Daily constraints
    for day in days:
        # Must be in at least one city each day
        solver.add(z3.Or(presence[day][0], presence[day][1], presence[day][2]))
        
        # Cannot be in all three cities simultaneously
        solver.add(z3.Not(z3.And(presence[day][0], presence[day][1], presence[day][2])))
        
        # Cannot be in Bucharest and Porto on the same day (no direct flight)
        solver.add(z3.Not(z3.And(presence[day][0], presence[day][2])))
    
    # Total days per city
    total_days = []
    for city_idx in range(len(cities)):
        total_days.append(z3.Sum([z3.If(presence[day][city_idx], 1, 0) for day in days]))
    solver.add(total_days[0] == 7)  # Bucharest
    solver.add(total_days[1] == 7)  # Lyon
    solver.add(total_days[2] == 4)  # Porto
    
    # Wedding constraint: Bucharest in first 7 days
    solver.add(z3.Or([presence[day][0] for day in range(7)]))
    
    # Connectivity constraints
    for day in range(num_days - 1):
        # Allow staying in same city or valid flight transition
        solver.add(z3.Or(
            # Stay in Bucharest
            z3.And(presence[day][0], presence[day+1][0]),
            # Stay in Lyon
            z3.And(presence[day][1], presence[day+1][1]),
            # Stay in Porto
            z3.And(presence[day][2], presence[day+1][2]),
            # Bucharest to Lyon flight
            z3.And(presence[day][0], presence[day+1][1], presence[day][0] == presence[day+1][0]),
            # Lyon to Porto flight
            z3.And(presence[day][1], presence[day+1][2], presence[day][1] == presence[day+1][1])
        ))
    
    # Solve the problem
    if solver.check() != z3.sat:
        print("No solution found")
        return
    
    model = solver.model()
    itinerary = []
    current_segment = {"cities": set(), "start": 0}
    
    # Build presence information from model
    presence_info = []
    for day in days:
        day_presence = []
        for city_idx, city in enumerate(cities):
            if z3.is_true(model.evaluate(presence[day][city_idx])):
                day_presence.append(city)
        presence_info.append(day_presence)
    
    # Create segments based on city presence
    for day in range(1, num_days):
        # Continue segment if same cities or flight transition
        if set(presence_info[day]) == set(presence_info[day-1]):
            continue
            
        # End current segment at previous day
        end_day = day - 1
        seg_cities = sorted(list(set(presence_info[end_day])))
        place = " and ".join(seg_cities)
        
        if current_segment["start"] == end_day:
            day_range = f"Day {current_segment['start']+1}"
        else:
            day_range = f"Day {current_segment['start']+1}-{end_day+1}"
        
        itinerary.append({"day_range": day_range, "place": place})
        current_segment = {"cities": set(presence_info[day]), "start": day}
    
    # Add last segment
    end_day = num_days - 1
    seg_cities = sorted(list(set(presence_info[end_day])))
    place = " and ".join(seg_cities)
    if current_segment["start"] == end_day:
        day_range = f"Day {end_day+1}"
    else:
        day_range = f"Day {current_segment['start']+1}-{end_day+1}"
    itinerary.append({"day_range": day_range, "place": place})
    
    print(json.dumps({'itinerary': itinerary}, indent=2))

if __name__ == "__main__":
    main()