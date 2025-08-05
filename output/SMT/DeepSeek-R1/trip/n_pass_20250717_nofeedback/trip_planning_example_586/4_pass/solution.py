from z3 import *

def main():
    # Define the City enumeration
    City = Datatype('City')
    City.declare('Naples')
    City.declare('Frankfurt')
    City.declare('Prague')
    City.declare('Lyon')
    City.declare('Helsinki')
    City = City.create()
    
    # Access city constants as attributes
    naples = City.Naples
    frankfurt = City.Frankfurt
    prague = City.Prague
    lyon = City.Lyon
    helsinki = City.Helsinki
    
    # Direct flights as tuples of City constants - ADDED HELSINKI-FRANKFURT CONNECTIONS
    direct_flights = [
        (frankfurt, lyon),
        (frankfurt, prague),
        (frankfurt, helsinki),  # Added connection
        (lyon, frankfurt),
        (lyon, prague),
        (naples, helsinki),
        (prague, frankfurt),
        (prague, lyon),
        (helsinki, naples),
        (helsinki, frankfurt)   # Added connection
    ]
    
    # Allowed transitions: same city or direct flight
    allowed_pairs = [(naples, naples), (frankfurt, frankfurt), (prague, prague), 
                    (lyon, lyon), (helsinki, helsinki)] + direct_flights
    
    # Create city variables for 14 days
    c = [Const(f'c_{i}', City) for i in range(14)]
    
    s = Solver()
    
    # Constraints: first and last day in Naples
    s.add(c[0] == naples)
    s.add(c[13] == naples)
    
    # Transition constraints between consecutive days
    for i in range(13):
        s.add(Or([And(c[i] == f, c[i+1] == t) for (f, t) in allowed_pairs]))
    
    # Count the days for each city
    count_frankfurt = Sum([If(c[i] == frankfurt, 1, 0) for i in range(14)])
    count_prague = Sum([If(c[i] == prague, 1, 0) for i in range(14)])
    count_lyon = Sum([If(c[i] == lyon, 1, 0) for i in range(14)])
    count_helsinki = Sum([If(c[i] == helsinki, 1, 0) for i in range(14)])
    
    s.add(count_frankfurt >= 3)
    s.add(count_prague >= 3)
    s.add(count_lyon >= 3)
    s.add(count_helsinki >= 2)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Extract the city for each day
        city_names = {
            naples: 'Naples',
            frankfurt: 'Frankfurt',
            prague: 'Prague',
            lyon: 'Lyon',
            helsinki: 'Helsinki'
        }
        day_cities = [city_names[m.evaluate(c[i])] for i in range(14)]
        
        # Group consecutive days into stays
        itinerary = []
        start_idx = 0
        for i in range(1, 14):
            if day_cities[i] != day_cities[i-1]:
                itinerary.append({
                    'day_range': f'Day {start_idx+1}-{i}',
                    'place': day_cities[i-1]
                })
                start_idx = i
        itinerary.append({
            'day_range': f'Day {start_idx+1}-14',
            'place': day_cities[13]
        })
        
        # Print the itinerary
        print("Plan found:", {'itinerary': itinerary})
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()