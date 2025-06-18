from z3 import *

def main():
    # Define the city enumeration
    City, (Prague, Berlin, Tallinn, Stockholm) = EnumSort('City', ['Prague', 'Berlin', 'Tallinn', 'Stockholm'])
    
    # Define the allowed direct flight pairs (symmetric)
    allowed_pairs = [
        (Berlin, Tallinn), (Tallinn, Berlin),
        (Prague, Tallinn), (Tallinn, Prague),
        (Stockholm, Tallinn), (Tallinn, Stockholm),
        (Prague, Stockholm), (Stockholm, Prague),
        (Stockholm, Berlin), (Berlin, Stockholm)
    ]
    
    # Create location variables for each day (L0 to L12)
    L = [ Const(f'L_{i}', City) for i in range(13) ]
    
    s = Solver()
    
    # Add travel constraints: for each day, either stay in the same city or travel via direct flight
    for d in range(12):
        stay_condition = (L[d] == L[d+1])
        travel_conditions = [ And(L[d] == c1, L[d+1] == c2) for (c1, c2) in allowed_pairs ]
        s.add(Or(stay_condition, Or(travel_conditions)))
    
    # Total days per city
    total_Prague = 0
    total_Berlin = 0
    total_Tallinn = 0
    total_Stockholm = 0
    
    # Each day d (from 0 to 11) corresponds to day d+1 in the itinerary
    for d in range(12):
        total_Prague += If(Or(L[d] == Prague, L[d+1] == Prague), 1, 0)
        total_Berlin += If(Or(L[d] == Berlin, L[d+1] == Berlin), 1, 0)
        total_Tallinn += If(Or(L[d] == Tallinn, L[d+1] == Tallinn), 1, 0)
        total_Stockholm += If(Or(L[d] == Stockholm, L[d+1] == Stockholm), 1, 0)
    
    s.add(total_Prague == 2)
    s.add(total_Berlin == 3)
    s.add(total_Tallinn == 5)
    s.add(total_Stockholm == 5)
    
    # Specific day constraints
    # Day 6: must be in Berlin (L5 or L6)
    s.add(Or(L[5] == Berlin, L[6] == Berlin))
    # Day 8: must be in Berlin (L7 or L8)
    s.add(Or(L[7] == Berlin, L[8] == Berlin))
    
    # Must be in Tallinn from day 8 to day 12 (days 8, 9, 10, 11, 12)
    # Day 8: uses L7 and L8
    s.add(Or(L[7] == Tallinn, L[8] == Tallinn))
    # Day 9: uses L8 and L9
    s.add(Or(L[8] == Tallinn, L[9] == Tallinn))
    # Day 10: uses L9 and L10
    s.add(Or(L[9] == Tallinn, L[10] == Tallinn))
    # Day 11: uses L10 and L11
    s.add(Or(L[10] == Tallinn, L[11] == Tallinn))
    # Day 12: uses L11 and L12
    s.add(Or(L[11] == Tallinn, L[12] == Tallinn))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        locs = [ m.evaluate(L[i]) for i in range(13) ]
        
        # Map the model to city names
        city_names = {
            Prague: 'Prague',
            Berlin: 'Berlin',
            Tallinn: 'Tallinn',
            Stockholm: 'Stockholm'
        }
        
        # Print the itinerary
        for day in range(12):
            start_city = locs[day]
            end_city = locs[day+1]
            start_name = city_names[start_city]
            end_name = city_names[end_city]
            
            if start_city == end_city:
                print(f"Day {day+1}: in {start_name}")
            else:
                # Sort city names alphabetically for consistent output
                cities = sorted([start_name, end_name])
                print(f"Day {day+1}: in {cities[0]} and {cities[1]}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()