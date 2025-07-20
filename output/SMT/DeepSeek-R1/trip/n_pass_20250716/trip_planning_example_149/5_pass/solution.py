from z3 import *

# Create city enumeration
City = Datatype('City')
City.declare('London')
City.declare('Santorini')
City.declare('Istanbul')
City = City.create()

# Create Z3 variables
s = Solver()

# Segment representation: (city, start_day, end_day)
segments = [
    (Const(f'seg1_city', City), Int(f'seg1_start'), Int(f'seg1_end')),
    (Const(f'seg2_city', City), Int(f'seg2_start'), Int(f'seg2_end')),
    (Const(f'seg3_city', City), Int(f'seg3_start'), Int(f'seg3_end')),
    (Const(f'seg4_city', City), Int(f'seg4_start'), Int(f'seg4_end')),
    (Const(f'seg5_city', City), Int(f'seg5_start'), Int(f'seg5_end'))
]

# Constraints for each segment
for i, (city, start, end) in enumerate(segments):
    # Valid city assignment
    s.add(Or(city == City.London, city == City.Santorini, city == City.Istanbul))
    # Valid day range (1-10)
    s.add(start >= 1, start <= 10)
    s.add(end >= 1, end <= 10)
    s.add(start <= end)
    
    # Segment must be used if start <= end
    if i > 0:
        # Previous segment must end before this segment starts
        s.add(Or(
            segments[i-1][2] < start,  # Previous ends before this starts
            segments[i-1][2] == -1      # Previous segment is unused
        ))
    
    # Mark unused segments (start > end)
    s.add(Or(start <= end, And(start == 11, end == -1)))

# Coverage of all days without gaps
for day in range(1, 11):
    covered = Or()
    for city, start, end in segments:
        covered = Or(covered, And(day >= start, day <= end, start <= end))
    s.add(covered)

# No overlapping segments
for i in range(len(segments)):
    for j in range(i+1, len(segments)):
        ci, si, ei = segments[i]
        cj, sj, ej = segments[j]
        s.add(Or(
            ei < sj,  # i ends before j starts
            ej < si,  # j ends before i starts
            si > ei,   # i is unused
            sj > ej    # j is unused
        ))

# Total days per city
london_days = 0
santorini_days = 0
istanbul_days = 0

for city, start, end in segments:
    # Calculate segment length
    seg_length = If(And(start >= 1, start <= end), end - start + 1, 0)
    
    # Accumulate days per city
    london_days = london_days + If(city == City.London, seg_length, 0)
    santorini_days = santorini_days + If(city == City.Santorini, seg_length, 0)
    istanbul_days = istanbul_days + If(city == City.Istanbul, seg_length, 0)

# Required days per city
s.add(london_days == 3)
s.add(santorini_days == 6)
s.add(istanbul_days == 3)

# Conference days in Santorini
santorini_days = []
for day in [5, 10]:
    in_santorini = Or()
    for city, start, end in segments:
        in_santorini = Or(in_santorini, And(city == City.Santorini, day >= start, day <= end, start <= end))
    s.add(in_santorini)

# Valid flight connections between segments
for i in range(len(segments) - 1):
    ci, si, ei = segments[i]
    cj, sj, ej = segments[j] = segments[i+1]
    
    # Only consider consecutive used segments
    valid_transition = Or(
        # Same city
        ci == cj,
        # London to Santorini
        And(ci == City.London, cj == City.Santorini),
        # Santorini to London
        And(ci == City.Santorini, cj == City.London),
        # London to Istanbul
        And(ci == City.London, cj == City.Istanbul),
        # Istanbul to London
        And(ci == City.Istanbul, cj == City.London)
    )
    
    # If both segments are used, require valid transition
    s.add(If(And(si <= ei, sj <= ej), valid_transition, True))

# Find and print a valid itinerary
if s.check() == sat:
    m = s.model()
    itinerary = [None] * 10  # Initialize empty itinerary for days 1-10
    
    # Extract segment information
    for i, (city, start, end) in enumerate(segments):
        city_val = m.eval(city)
        start_val = m.eval(start).as_long()
        end_val = m.eval(end).as_long()
        
        if start_val <= end_val and 1 <= start_val <= 10:
            city_name = "London" if city_val == City.London else \
                        "Santorini" if city_val == City.Santorini else "Istanbul"
            # Fill in the itinerary
            for day in range(start_val, end_val + 1):
                itinerary[day-1] = city_name
    
    # Print the 10-day itinerary
    print("Valid 10-day itinerary found:")
    for day, city in enumerate(itinerary, start=1):
        print(f"Day {day}: {city}")
    
    # Print segment information
    print("\nSegments:")
    for i, (city, start, end) in enumerate(segments):
        city_val = m.eval(city)
        start_val = m.eval(start).as_long()
        end_val = m.eval(end).as_long()
        if start_val <= end_val and 1 <= start_val <= 10:
            city_name = "London" if city_val == City.London else \
                        "Santorini" if city_val == City.Santorini else "Istanbul"
            print(f"Segment {i+1}: {city_name} (Days {start_val}-{end_val})")
        else:
            print(f"Segment {i+1}: Unused")
else:
    print("No valid itinerary exists for the given constraints.")