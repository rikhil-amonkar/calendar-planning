from z3 import *

def main():
    # Create the solver
    s = Solver()
    
    # Define the cities: 0=Dublin, 1=Riga, 2=Vilnius
    S1 = Int('S1')
    S2 = Int('S2')
    S3 = Int('S3')
    t1 = Int('t1')
    t2 = Int('t2')
    
    # Constraints for cities: must be 0, 1, or 2 and distinct
    s.add(S1 >= 0, S1 <= 2)
    s.add(S2 >= 0, S2 <= 2)
    s.add(S3 >= 0, S3 <= 2)
    s.add(Distinct(S1, S2, S3))
    
    # Constraints for travel days: 1 <= t1 < t2 <= 11
    s.add(t1 >= 1, t1 <= 11)
    s.add(t2 >= 1, t2 <= 11)
    s.add(t1 < t2)
    
    # Days in each city
    days_dublin = If(S1 == 0, t1, 
                    If(S2 == 0, t2 - t1 + 1,
                     If(S3 == 0, 13 - t2, 0)))
    days_riga   = If(S1 == 1, t1,
                    If(S2 == 1, t2 - t1 + 1,
                     If(S3 == 1, 13 - t2, 0)))
    days_vilnius= If(S1 == 2, t1,
                    If(S2 == 2, t2 - t1 + 1,
                     If(S3 == 2, 13 - t2, 0)))
    
    s.add(days_dublin == 2)
    s.add(days_riga == 5)
    s.add(days_vilnius == 7)
    
    # Flight constraints
    # Allowed flights: (Dublin,Riga), (Riga,Dublin), (Riga,Vilnius)
    flight1_ok = Or(
        And(S1 == 0, S2 == 1),  # Dublin -> Riga
        And(S1 == 1, S2 == 0),  # Riga -> Dublin
        And(S1 == 1, S2 == 2)   # Riga -> Vilnius
    )
    flight2_ok = Or(
        And(S2 == 0, S3 == 1),  # Dublin -> Riga
        And(S2 == 1, S3 == 0),  # Riga -> Dublin
        And(S2 == 1, S3 == 2)   # Riga -> Vilnius
    )
    s.add(flight1_ok, flight2_ok)
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        S1_val = m[S1].as_long()
        S2_val = m[S2].as_long()
        S3_val = m[S3].as_long()
        t1_val = m[t1].as_long()
        t2_val = m[t2].as_long()
        
        city_names = {0: 'Dublin', 1: 'Riga', 2: 'Vilnius'}
        s1_name = city_names[S1_val]
        s2_name = city_names[S2_val]
        s3_name = city_names[S3_val]
        
        # Build the plan for each day
        plan = []
        for day in range(1, 13):
            if day < t1_val:
                cities_today = [s1_name]
            elif day == t1_val:
                cities_today = [s1_name, s2_name]
            elif day < t2_val:
                cities_today = [s2_name]
            elif day == t2_val:
                cities_today = [s2_name, s3_name]
            else:  # day > t2_val
                cities_today = [s3_name]
            plan.append((day, cities_today))
        
        # Print the plan
        for day, cities in plan:
            print(f"Day {day}: {', '.join(cities)}")
    else:
        print("No valid plan found.")

if __name__ == '__main__':
    main()