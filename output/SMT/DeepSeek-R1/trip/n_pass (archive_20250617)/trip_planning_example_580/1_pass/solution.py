from z3 import *

def main():
    # Define the City enum
    City, (Paris, Oslo, Porto, Geneva, Reykjavik) = EnumSort('City', ['Paris', 'Oslo', 'Porto', 'Geneva', 'Reykjavik'])
    
    # Create end_city variables for 24 positions (0 to 23)
    end_city = [Const('end_city_%d' % i, City) for i in range(24)]
    
    s = Solver()
    
    # Fix the first 7 days (indices 0 to 6) to Geneva
    for i in range(0, 7):
        s.add(end_city[i] == Geneva)
    
    # From index 7 to 23, we cannot be in Geneva
    for i in range(7, 24):
        s.add(end_city[i] != Geneva)
    
    # Define the flight constraints: direct flights
    def flight_ok(c1, c2):
        return Or(
            And(c1 == Paris, Or(c2 == Oslo, c2 == Porto, c2 == Geneva, c2 == Reykjavik)),
            And(c1 == Oslo, Or(c2 == Paris, c2 == Geneva, c2 == Reykjavik, c2 == Porto)),
            And(c1 == Porto, Or(c2 == Paris, c2 == Geneva, c2 == Oslo)),
            And(c1 == Geneva, Or(c2 == Oslo, c2 == Paris, c2 == Porto)),
            And(c1 == Reykjavik, Or(c2 == Paris, c2 == Oslo))
        )
    
    # Travel constraints for days 1 to 23
    for i in range(1, 24):
        c1 = end_city[i-1]
        c2 = end_city[i]
        s.add(If(c1 != c2, flight_ok(c1, c2), True))
    
    # Total days in each city
    total_paris = 0
    total_oslo = 0
    total_porto = 0
    total_geneva = 0
    total_reykjavik = 0
    
    for i in range(1, 24):  # days 1 to 23
        total_paris += If(Or(end_city[i-1] == Paris, end_city[i] == Paris), 1, 0)
        total_oslo += If(Or(end_city[i-1] == Oslo, end_city[i] == Oslo), 1, 0)
        total_porto += If(Or(end_city[i-1] == Porto, end_city[i] == Porto), 1, 0)
        total_geneva += If(Or(end_city[i-1] == Geneva, end_city[i] == Geneva), 1, 0)
        total_reykjavik += If(Or(end_city[i-1] == Reykjavik, end_city[i] == Reykjavik), 1, 0)
    
    s.add(total_paris == 6)
    s.add(total_oslo == 5)
    s.add(total_porto == 7)
    s.add(total_geneva == 7)
    s.add(total_reykjavik == 2)
    
    # Constraint: Oslo must be visited between days 19 and 23 (inclusive)
    oslo_presence = []
    for day in [19, 20, 21, 22, 23]:
        oslo_presence.append(Or(end_city[day-1] == Oslo, end_city[day] == Oslo))
    s.add(Or(oslo_presence))
    
    # Check and output
    if s.check() == sat:
        m = s.model()
        res = [m[end_city[i]] for i in range(24)]
        
        # Map the constants to their names
        city_names = {
            Paris: "Paris",
            Oslo: "Oslo",
            Porto: "Porto",
            Geneva: "Geneva",
            Reykjavik: "Reykjavik"
        }
        
        for day in range(1, 24):
            start_city = res[day-1]
            end_city_val = res[day]
            start_name = city_names[start_city]
            end_name = city_names[end_city_val]
            if start_city.eq(end_city_val):
                print(f"Day {day}: Stay in {start_name}")
            else:
                print(f"Day {day}: Travel from {start_name} to {end_name}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()