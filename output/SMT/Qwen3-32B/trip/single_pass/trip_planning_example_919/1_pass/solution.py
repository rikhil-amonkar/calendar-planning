from z3 import *
import json

def main():
    cities = ['Vienna', 'Milan', 'Rome', 'Riga', 'Lisbon', 'Vilnius', 'Oslo']
    num_cities = len(cities)
    days_in_city = {
        'Vienna': 4,
        'Milan': 2,
        'Rome': 3,
        'Riga': 2,
        'Lisbon': 3,
        'Vilnius': 4,
        'Oslo': 3,
    }

    # Define allowed flights
    original_allowed = [
        ('Riga', 'Oslo'),
        ('Rome', 'Oslo'),
        ('Vienna', 'Milan'),
        ('Vienna', 'Vilnius'),
        ('Vienna', 'Lisbon'),
        ('Riga', 'Milan'),
        ('Lisbon', 'Oslo'),
        ('Rome', 'Riga'),
        ('Rome', 'Lisbon'),
        ('Vienna', 'Riga'),
        ('Vienna', 'Rome'),
        ('Milan', 'Oslo'),
        ('Vienna', 'Oslo'),
        ('Vilnius', 'Oslo'),
        ('Riga', 'Vilnius'),
        ('Vilnius', 'Milan'),
        ('Riga', 'Lisbon'),
        ('Milan', 'Lisbon'),
    ]
    allowed_flights = set()
    for a, b in original_allowed:
        allowed_flights.add((a, b))
        allowed_flights.add((b, a))

    s = Solver()

    # Create variables for the sequence of cities
    seq = [String(f'seq_{i}') for i in range(num_cities)]

    # All cities in the sequence must be distinct and in the cities list
    for i in range(num_cities):
        s.add(Or([seq[i] == city for city in cities]))

    # All distinct
    s.add(Distinct(seq))

    # First city must be Vienna
    s.add(seq[0] == 'Vienna')

    # Add constraints for allowed flights between consecutive cities
    for i in range(num_cities - 1):
        constraints = []
        for (a, b) in allowed_flights:
            constraints.append(And(seq[i] == a, seq[i+1] == b))
        s.add(Or(constraints))

    # Create start_day and end_day variables
    start_day = [Int(f'start_day_{i}') for i in range(num_cities)]
    end_day = [Int(f'end_day_{i}') for i in range(num_cities)]

    # Add constraints for start_day and end_day
    for i in range(num_cities):
        # Compute days_in_city for seq[i]
        days_i = If(seq[i] == 'Vienna', 4,
                    If(seq[i] == 'Milan', 2,
                       If(seq[i] == 'Rome', 3,
                          If(seq[i] == 'Riga', 2,
                             If(seq[i] == 'Lisbon', 3,
                                If(seq[i] == 'Vilnius', 4,
                                   If(seq[i] == 'Oslo', 3, 0))))))  # 0 is invalid, but constraints ensure valid
        s.add(end_day[i] == start_day[i] + days_i - 1)

    # start_day[0] is 1
    s.add(start_day[0] == 1)

    # For i >=1, start_day[i] = end_day[i-1]
    for i in range(1, num_cities):
        s.add(start_day[i] == end_day[i-1])

    # end_day of last city is 15
    s.add(end_day[num_cities - 1] == 15)

    # Constraints for Lisbon and Oslo
    for i in range(num_cities):
        # Lisbon constraint: if city is Lisbon, then start_day <=13 and end_day >=11
        s.add(Or(seq[i] != 'Lisbon', And(start_day[i] <= 13, end_day[i] >= 11)))
        # Oslo constraint: if city is Oslo, then start_day <=15 and end_day >=13
        s.add(Or(seq[i] != 'Oslo', And(start_day[i] <= 15, end_day[i] >= 13)))

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        # Extract the sequence
        sequence = [model.eval(seq[i]).as_string() for i in range(num_cities)]
        # Extract start_day and end_day
        start_days = [model.eval(start_day[i]).as_long() for i in range(num_cities)]
        end_days = [model.eval(end_day[i]).as_long() for i in range(num_cities)]

        # Generate the itinerary
        itinerary = []
        for i in range(num_cities):
            city = sequence[i]
            s_day = start_days[i]
            e_day = end_days[i]
            for day in range(s_day, e_day + 1):
                itinerary.append({'day': day, 'city': city})

        # Sort the itinerary by day
        itinerary.sort(key=lambda x: x['day'])

        # Output as JSON
        print(json.dumps({'itinerary': itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()