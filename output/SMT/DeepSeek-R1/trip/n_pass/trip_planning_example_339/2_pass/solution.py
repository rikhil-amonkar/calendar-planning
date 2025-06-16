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
    for d in range(0, 16):  # d: index for TravelDest (0 to 15) representing day1 to day16
        s.add(Or(
            TravelDest[d] == -1,
            And(TravelDest[d] >= 0, TravelDest[d] <= 3, TravelDest[d] != BaseCity[d])
        ))
    
    # BaseCity propagation: BaseCity[d] = (TravelDest[d-1] if not -1 else BaseCity[d-1])
    for d in range(1, 17):  # d: index for BaseCity from 1 to 16 (day2 to day17)
        # BaseCity[d] = if TravelDest[d-1] != -1 then TravelDest[d-1] else BaseCity[d-1]
        s.add(BaseCity[d] == If(TravelDest[d-1] != -1, TravelDest[d-1], BaseCity[d-1]))
    
    # After day2, BaseCity cannot be Warsaw (0) (for day3 to day17)
    for d in range(2, 17):  # BaseCity indices 2 to 16 (day3 to day17)
        s.add(BaseCity[d] != 0)
    
    # Flight connection constraints for travel days
    for d in range(0, 16):  # d: index for TravelDest (0 to 15) representing day1 to day16
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
            day_index = d - 1
            if d < 17:
                # On day d, we are in BaseCity[day_index] and if we travel, also in TravelDest[day_index]
                in_city[(c, d)] = Or(
                    BaseCity[day_index] == c,
                    And(TravelDest[day_index] != -1, TravelDest[day_index] == c)
                )
            else:
                # Day17: no travel defined, so only BaseCity[16]
                in_city[(c, d)] = (BaseCity[16] == c)
    
    # Total days per city
    total_days = [0] * 4
    for c in range(4):
        total = 0
        for d in range(1, 18):
            total += If(in_city[(c, d)], 1, 0)
        s.add(total == [2, 7, 7, 4][c])
    
    # Wedding constraint: must be in Riga every day from day11 to day17
    for d in range(11, 18):
        s.add(in_city[(1, d)])
    
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