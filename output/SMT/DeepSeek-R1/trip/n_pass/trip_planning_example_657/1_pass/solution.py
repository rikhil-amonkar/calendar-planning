from z3 import *

def main():
    # Define the segment assignment variables
    seg0 = Int('seg0')
    seg1 = Int('seg1')
    seg2 = Int('seg2')
    seg3 = Int('seg3')
    
    # Mapping city names to integers
    mapping = {
        'Manchester': 0,
        'Valencia': 1,
        'Naples': 2,
        'Oslo': 3,
        'Vilnius': 4,
        'Frankfurt': 5
    }
    
    # Reverse mapping for output
    rev_mapping = {
        0: 'Manchester',
        1: 'Valencia',
        2: 'Naples',
        3: 'Oslo',
        4: 'Vilnius',
        5: 'Frankfurt'
    }
    
    # Given flight connections (undirected)
    flight_strings = [
        ('Valencia', 'Frankfurt'), 
        ('Manchester', 'Frankfurt'),
        ('Naples', 'Manchester'),
        ('Naples', 'Frankfurt'),
        ('Naples', 'Oslo'),
        ('Oslo', 'Frankfurt'),
        ('Vilnius', 'Frankfurt'),
        ('Oslo', 'Vilnius'),
        ('Manchester', 'Oslo'),
        ('Valencia', 'Naples')
    ]
    
    # Convert to directed flights in integer form
    directed_flights = []
    for a, b in flight_strings:
        a_int = mapping[a]
        b_int = mapping[b]
        directed_flights.append((a_int, b_int))
        directed_flights.append((b_int, a_int))
    
    # Create solver
    s = Solver()
    
    # Constraints: seg0, seg1, seg2, seg3 in [0,3] and distinct
    s.add(And(seg0 >= 0, seg0 <= 3))
    s.add(And(seg1 >= 0, seg1 <= 3))
    s.add(And(seg2 >= 0, seg2 <= 3))
    s.add(And(seg3 >= 0, seg3 <= 3))
    s.add(Distinct(seg0, seg1, seg2, seg3))
    
    # Define required days for each city
    req0 = If(seg0 == 0, 4, If(seg0 == 1, 4, If(seg0 == 2, 4, 3)))
    req1 = If(seg1 == 0, 4, If(seg1 == 1, 4, If(seg1 == 2, 4, 3)))
    req2 = If(seg2 == 0, 4, If(seg2 == 1, 4, If(seg2 == 2, 4, 3)))
    req3 = If(seg3 == 0, 4, If(seg3 == 1, 4, If(seg3 == 2, 4, 3)))
    
    # Calculate segment end days
    T1 = req0
    T2 = T1 + req1 - 1
    T3 = T2 + req2 - 1
    s.add(T3 == 13 - req3)
    
    # Flight constraints for the entire sequence
    cities_sequence = [seg0, seg1, seg2, seg3, 4, 5]  # 4=Vilnius, 5=Frankfurt
    for i in range(5):
        a = cities_sequence[i]
        b = cities_sequence[i+1]
        s.add(Or([And(a == flight[0], b == flight[1]) for flight in directed_flights]))
    
    # Additional bounds for T1, T2, T3
    s.add(T1 >= 1, T1 <= 12)
    s.add(T2 >= T1, T2 <= 12)
    s.add(T3 >= T2, T3 <= 12)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        seg0_val = m[seg0].as_long()
        seg1_val = m[seg1].as_long()
        seg2_val = m[seg2].as_long()
        seg3_val = m[seg3].as_long()
        T1_val = m.evaluate(T1).as_long()
        T2_val = m.evaluate(T2).as_long()
        T3_val = m.evaluate(T3).as_long()
        
        # Get city names
        city0 = rev_mapping[seg0_val]
        city1 = rev_mapping[seg1_val]
        city2 = rev_mapping[seg2_val]
        city3 = rev_mapping[seg3_val]
        
        # Output the plan
        print("From day 1 to day {}: stay in {}".format(T1_val, city0))
        print("From day {} to day {}: stay in {}".format(T1_val, T2_val, city1))
        print("From day {} to day {}: stay in {}".format(T2_val, T3_val, city2))
        print("From day {} to day 12: stay in {}".format(T3_val, city3))
        print("From day 12 to day 13: stay in Vilnius")
        print("From day 13 to day 16: stay in Frankfurt")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()