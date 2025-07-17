from z3 import *

def solve_itinerary():
    s = Solver()

    # Fixed Naples segment (days 1-5)
    naples_days = [(1, 5)]

    # Variable segments for Vienna and Vilnius
    # We'll model them as start/end days
    vienna1_start = Int('vienna1_start')
    vienna1_end = Int('vienna1_end')
    vilnius_start = Int('vilnius_start')
    vilnius_end = Int('vilnius_end')
    vienna2_start = Int('vienna2_start')
    vienna2_end = Int('vienna2_end')

    # Constraints
    # 1. Naples is days 1-5
    # 2. First flight is Naples to Vienna on day 5
    s.add(vienna1_start == 5)
    # 3. Vienna must connect to Vilnius
    s.add(vilnius_start == vienna1_end + 1)
    # 4. Vilnius must connect back to Vienna
    s.add(vienna2_start == vilnius_end + 1)
    # 5. Total days is 17
    s.add(vienna2_end == 17)
    # 6. Segment ordering
    s.add(vienna1_start <= vienna1_end)
    s.add(vilnius_start <= vilnius_end)
    s.add(vienna2_start <= vienna2_end)
    # 7. Day counts
    s.add(vienna1_end - vienna1_start + 1 + vienna2_end - vienna2_start + 1 == 7)  # Vienna total
    s.add(vilnius_end - vilnius_start + 1 == 7)  # Vilnius total

    if s.check() == sat:
        m = s.model()
        # Extract values
        v1s = m.evaluate(vienna1_start).as_long()
        v1e = m.evaluate(vienna1_end).as_long()
        vs = m.evaluate(vilnius_start).as_long()
        ve = m.evaluate(vilnius_end).as_long()
        v2s = m.evaluate(vienna2_start).as_long()
        v2e = m.evaluate(vienna2_end).as_long()

        # Build itinerary
        itinerary = []
        # Naples days
        for day in range(1, 6):
            itinerary.append({'day': day, 'place': 'Naples'})
        # First Vienna segment
        for day in range(v1s, v1e + 1):
            itinerary.append({'day': day, 'place': 'Vienna'})
        # Vilnius segment
        for day in range(vs, ve + 1):
            itinerary.append({'day': day, 'place': 'Vilnius'})
        # Second Vienna segment
        for day in range(v2s, v2e + 1):
            itinerary.append({'day': day, 'place': 'Vienna'})

        # Verify counts
        naples_count = len([x for x in itinerary if x['place'] == 'Naples'])
        vienna_count = len([x for x in itinerary if x['place'] == 'Vienna'])
        vilnius_count = len([x for x in itinerary if x['place'] == 'Vilnius'])
        assert naples_count == 5
        assert vienna_count == 7
        assert vilnius_count == 7
        assert len({x['day'] for x in itinerary}) == 17  # All days accounted for

        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No solution found")