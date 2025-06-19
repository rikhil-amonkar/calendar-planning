from z3 import *

def main():
    s = Solver()
    
    # Cities: 0=Dublin, 1=Riga, 2=Vilnius
    S1 = Int('S1')
    S2 = Int('S2')
    S3 = Int('S3')
    t1 = Int('t1')
    t2 = Int('t2')
    
    s.add(S1 >= 0, S1 <= 2)
    s.add(S2 >= 0, S2 <= 2)
    s.add(S3 >= 0, S3 <= 2)
    s.add(Distinct(S1, S2, S3))
    s.add(S3 == 2)  # Last city must be Vilnius (no outgoing flights)
    
    s.add(t1 >= 1, t1 <= 11)
    s.add(t2 >= 2, t2 <= 12)
    s.add(t1 < t2)
    
    # Days in each city
    dublin_days = If(S1 == 0, t1, 0) + If(S2 == 0, t2 - t1 + 1, 0)
    riga_days   = If(S1 == 1, t1, 0) + If(S2 == 1, t2 - t1 + 1, 0)
    vilnius_days = 13 - t2  # Since S3 is Vilnius
    
    s.add(dublin_days == 2)
    s.add(riga_days == 5)
    s.add(vilnius_days == 7)
    
    # Flight constraints
    flight1 = Or(
        And(S1 == 0, S2 == 1),  # Dublin -> Riga
        And(S1 == 1, S2 == 0),   # Riga -> Dublin
        And(S1 == 1, S2 == 2)    # Riga -> Vilnius
    )
    flight2 = Or(
        And(S2 == 0, S3 == 1),   # Dublin -> Riga
        And(S2 == 1, S3 == 0),   # Riga -> Dublin
        And(S2 == 1, S3 == 2)    # Riga -> Vilnius
    )
    s.add(flight1, flight2)
    
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
        
        plan = []
        for day in range(1, 13):
            if day < t1_val:
                cities = [s1_name]
            elif day == t1_val:
                cities = [s1_name, s2_name]
            elif day < t2_val:
                cities = [s2_name]
            elif day == t2_val:
                cities = [s2_name, s3_name]
            else:
                cities = [s3_name]
            plan.append((day, cities))
        
        for day, cities in plan:
            print(f"Day {day}: {', '.join(cities)}")
    else:
        print("No valid plan found.")

if __name__ == '__main__':
    main()