from z3 import *

# Define city constraints
cities = ['Berlin', 'Split', 'Lyon', 'Bucharest', 'Lisbon', 'Riga', 'Tallinn']
min_days = {
    'Berlin': 3,
    'Split': 1,
    'Lyon': 3,
    'Bucharest': 1,
    'Lisbon': 1,
    'Riga': 3,
    'Tallinn': 3
}
max_days = {
    'Berlin': 5,
    'Split': 3,
    'Lyon': 5,
    'Bucharest': 3,
    'Lisbon': 3,
    'Riga': 5,
    'Tallinn': 5
}

n = 7  # Number of segments (one per city)
Segment = Datatype('Segment')
Segment.declare('segment', ('city', StringSort()), ('start', IntSort()), ('end', IntSort()))
Segment = Segment.create()
segments = [Const(f'segment_{i}', Segment) for i in range(n)]

s = Solver()

# Each segment's city must be one of the predefined cities
for seg in segments:
    s.add(Or([Segment.city(seg) == city for city in cities]))

# All cities must be distinct
s.add(Distinct([Segment.city(seg) for seg in segments]))

# Trip starts at day 1 and ends at day 22
s.add(Segment.start(segments[0]) == 1)
s.add(Segment.end(segments[n-1]) == 22)

# Segments must be contiguous: end of current + 1 = start of next
for i in range(n-1):
    s.add(Segment.end(segments[i]) + 1 == Segment.start(segments[i+1]))

# Duration of each segment must satisfy min and max days for its city
for seg in segments:
    city = Segment.city(seg)
    start = Segment.start(seg)
    end = Segment.end(seg)
    duration = end - start + 1
    for c in cities:
        s.add(Implies(city == c, And(duration >= min_days[c], duration <= max_days[c])))

# Start and end days must be valid (1-22, start <= end)
for seg in segments:
    s.add(Segment.start(seg) >= 1)
    s.add(Segment.end(seg) <= 22)
    s.add(Segment.start(seg) <= Segment.end(seg))

# Critical: Total days must sum exactly to 22
total_days = 0
for seg in segments:
    total_days += (Segment.end(seg) - Segment.start(seg) + 1)
s.add(total_days == 22)

# Solve and output itinerary
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(n):
        seg = segments[i]
        city_val = m.evaluate(Segment.city(seg))
        start_val = m.evaluate(Segment.start(seg))
        end_val = m.evaluate(Segment.end(seg))
        itinerary.append({'day_range': f"Day {start_val}-{end_val}", 'place': str(city_val)})
    print({'itinerary': itinerary})
else:
    print("No valid itinerary found.")