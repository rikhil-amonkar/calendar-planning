from z3 import *

def main():
    # City mapping: 0=Warsaw, 1=Riga, 2=Budapest, 3=Paris
    city_names = ["Warsaw", "Riga", "Budapest", "Paris"]
    
    # Flight connections: symmetric and without self-loops
    def connected(i, j):
        return Or(
            And(i == 0, Or(j == 1, j == 2, j == 3)),
            And(i == 1, Or(j == 0, j == 3)),
            And(i == 2, Or(j == 0, j == 3)),
            And(i == 3, Or(j == 0, j == 1, j == 2))
        )
    
    # Create Z3 variables for 17 days of BaseCity and 16 days of TravelDest
    BaseCity = [Int(f'BaseCity_{d}') for d in range(1, 18)]
    TravelDest = [Int(f'TravelDest_{d}') for d in range(1, 17)]
    
    s = Solver()
    
    # Constraint: BaseCity[0] (day1) is Warsaw (0)
    s.add(BaseCity[0] == 0)
    # Constraint: No travel on day1 (TravelDest[0] = -1)
    s.add(TravelDest[0] == -1)
    
    # Domain constraints for BaseCity and TravelDest
    for i in range(17):
        s.add(BaseCity[i] >= 0, BaseCity[i] <= 3)
    for i in range(16):
        s.add(TravelDest[i] >= -1, TravelDest[i] <= 3)
    
    # TravelDest constraints: if not -1, must be a valid city and not same as BaseCity
    for d in range(1, 16):  # d: day index for TravelDest (1 to 15, representing day2 to day16)
        s.add(Or(
            TravelDest[d] == -1,
            And(TravelDest[d] >= 0, TravelDest[d] <= 3, TravelDest[d] != BaseCity[d])
        ))
    
    # BaseCity propagation: BaseCity[d] = (TravelDest[d-1] if not -1 else BaseCity[d-1])
    for d in range(2, 18):  # d: day index from 2 to 17
        prev_travel = TravelDest[d-2]  # TravelDest for day d-1 (index d-2)
        s.add(BaseCity[d-1] == If(prev_travel != -1, prev_travel, BaseCity[d-2]))
    
    # After day2, BaseCity cannot be Warsaw (0)
    for d in range(3, 18):  # days 3 to 17
        s.add(BaseCity[d-1] != 0)
    
    # Flight connection constraints for travel days
    for d in range(0, 16):  # d: index for TravelDest (0 to 15) representing day1 to day16
        # For day1, TravelDest[0] is -1 (no constraint). For others, if TravelDest[d] != -1, check connection.
        s.add(If(
            TravelDest[d] != -1,
            connected(BaseCity[d], TravelDest[d]),
            True
        ))
    
    # Total travel days must be 3 (including day2)
    travel_days = [If(TravelDest[d] != -1, 1, 0) for d in range(0, 16)]
    s.add(Sum(travel_days) == 3)
    
    # Define in_city: for each city and day, whether present
    in_city = {}
    for c in range(4):
        for d in range(1, 18):
            if d < 17:
                # TravelDest index d-1 exists for day d
                in_city[(c, d)] = Or(
                    BaseCity[d-1] == c,
                    And(TravelDest[d-1] != -1, TravelDest[d-1] == c)
                )
            else:
                # Day17: no travel defined, so only BaseCity
                in_city[(c, d)] = (BaseCity[16] == c)
    
    # Total days per city
    total_days = [0] * 4
    for c in range(4):
        total = 0
        for d in range(1, 18):
            total += If(in_city[(c, d)], 1, 0)
        s.add(total == [2, 7, 7, 4][c])
    
    # Wedding constraint: at least one day in Riga (city1) between days 11 and 17
    s.add(Or([in_city[(1, d)] for d in range(11, 18)]))
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        # Output the itinerary
        print("Day-by-Day Itinerary:")
        for d in range(1, 18):
            cities_today = []
            for c in range(4):
                if m.evaluate(in_city[(c, d)]):
                    cities_today.append(city_names[c])
            print(f"Day {d}: {', '.join(cities_today)}")
    else:
        print("No valid plan found.")

if __name__ == "__main__":
    main()