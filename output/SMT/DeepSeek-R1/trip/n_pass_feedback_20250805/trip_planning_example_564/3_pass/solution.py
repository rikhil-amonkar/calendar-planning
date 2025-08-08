from z3 import *

def main():
    # Define the City enumeration
    City = Datatype('City')
    City.declare('Istanbul')
    City.declare('Rome')
    City.declare('Seville')
    City.declare('Naples')
    City.declare('Santorini')
    City = City.create()
    
    # Create variables for each day: c[0] to c[15] represent the end city of day 1 to day 16.
    c = [Const('c_%d' % i, City) for i in range(16)]
    
    s = Solver()
    
    # Direct flights as an undirected graph: list of pairs (city1, city2)
    direct_flights = [
        (City.Rome, City.Santorini),
        (City.Rome, City.Seville),
        (City.Istanbul, City.Naples),
        (City.Naples, City.Santorini),
        (City.Rome, City.Naples),
        (City.Rome, City.Istanbul)
    ]
    # Make the flight set symmetric: include both (a,b) and (b,a)
    flight_set = set()
    for (a, b) in direct_flights:
        flight_set.add((a, b))
        flight_set.add((b, a))
    
    # Constraint 1: Flight constraints between consecutive days
    for i in range(15):
        # If the city changes from day i to day i+1, ensure there's a direct flight
        allowed = Or(c[i] == c[i+1])
        for (a, b) in flight_set:
            allowed = Or(allowed, And(c[i] == a, c[i+1] == b))
        s.add(allowed)
    
    # Required days for each city
    required_days = {
        City.Istanbul: 2,
        City.Rome: 3,
        City.Seville: 4,
        City.Naples: 7,
        City.Santorini: 4
    }
    
    # Create a dictionary to hold the in_city expressions for each city
    in_city_dict = {}
    for city in [City.Istanbul, City.Rome, City.Seville, City.Naples, City.Santorini]:
        in_x = []
        for day in range(16):
            if day == 0:
                in_x.append(c[0] == city)
            else:
                in_x.append(Or(c[day-1] == city, c[day] == city))
        in_city_dict[city] = in_x
    
    # Constraint 2: Total days per city (using the in_city arrays)
    for city, in_x in in_city_dict.items():
        total = 0
        for i in range(16):
            total += If(in_x[i], 1, 0)
        s.add(total == required_days[city])
    
    # Constraint 3: Santorini wedding (must be in Santorini on days 13, 14, 15, 16)
    in_santorini = in_city_dict[City.Santorini]
    s.add(in_santorini[12])  # Day 13
    s.add(in_santorini[13])  # Day 14
    s.add(in_santorini[14])  # Day 15
    s.add(in_santorini[15])  # Day 16
    
    # Constraint 4: Istanbul relatives (must be in Istanbul on day 6 or day 7)
    in_istanbul = in_city_dict[City.Istanbul]
    s.add(Or(in_istanbul[5], in_istanbul[6]))  # Day 6 or 7
    
    # Constraint 5: Consecutive block for each city
    for city, in_x in in_city_dict.items():
        # For every triple i, j, k with i < k < j, if in_x[i] and in_x[j] are True, then in_x[k] must be True.
        for i in range(16):
            for j in range(i+2, 16):
                for k in range(i+1, j):
                    s.add(Implies(And(in_x[i], in_x[j]), in_x[k]))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        blocks = []
        # Map Z3 city constants to string names
        city_names = {
            City.Istanbul: "Istanbul",
            City.Rome: "Rome",
            City.Seville: "Seville",
            City.Naples: "Naples",
            City.Santorini: "Santorini"
        }
        
        # For each city, find the contiguous block
        for city in [City.Istanbul, City.Rome, City.Seville, City.Naples, City.Santorini]:
            in_x = in_city_dict[city]
            days_in_city = []
            for day in range(16):
                if model.eval(in_x[day]):
                    days_in_city.append(day+1)  # day index to day number
            if days_in_city:
                start_day = days_in_city[0]
                end_day = days_in_city[-1]
                blocks.append({
                    'start': start_day,
                    'end': end_day,
                    'place': city_names[city]
                })
        
        # Sort the blocks by the start day
        blocks_sorted = sorted(blocks, key=lambda x: x['start'])
        itinerary = []
        for blk in blocks_sorted:
            day_range = f"Day {blk['start']}-{blk['end']}"
            itinerary.append({'day_range': day_range, 'place': blk['place']})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()