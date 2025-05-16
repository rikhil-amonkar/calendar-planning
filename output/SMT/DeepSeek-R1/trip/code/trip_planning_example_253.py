from z3 import *

# Define cities and their integer representations
City = Datatype('City')
City.declare('Vienna')
City.declare('Santorini')
City.declare('Amsterdam')
City.declare('Lyon')
City = City.create()

# Direct flight pairs (bidirectional)
flights = [
    (City.Vienna, City.Lyon),
    (City.Vienna, City.Santorini),
    (City.Vienna, City.Amsterdam),
    (City.Amsterdam, City.Santorini),
    (City.Lyon, City.Amsterdam),
    # Add reverse directions
    (City.Lyon, City.Vienna),
    (City.Santorini, City.Vienna),
    (City.Amsterdam, City.Vienna),
    (City.Santorini, City.Amsterdam),
    (City.Amsterdam, City.Lyon),
]

s = Solver()

# Define segments and cities
pre_lyon = Const('pre_lyon', City)  # City before Lyon (days 1-6)
post_ams = Const('post_ams', City)   # City after Amsterdam (days 12-14)

# Pre-Lyon constraints: must connect to Lyon via flight
s.add(Or(pre_lyon == City.Vienna, pre_lyon == City.Amsterdam))  # Possible cities with flights to Lyon
s.add(Or([And(pre_lyon == a, City.Lyon == b) for (a, b) in flights]))

# Post-Amsterdam constraints: must connect from Amsterdam via flight
s.add(Or(post_ams == City.Santorini, post_ams == City.Vienna))  # Possible cities with flights from Amsterdam
s.add(Or([And(City.Amsterdam == a, post_ams == b) for (a, b) in flights]))

# Duration constraints with flight day overlaps
# Vienna needs 7 days total
vienna_days = 0
# If Vienna is pre_lyon: days 1-6 (6 days) + flight day 7
vienna_days += If(pre_lyon == City.Vienna, 6 + 1, 0)
# If Vienna is post_ams: days 12-14 (3 days)
vienna_days += If(post_ams == City.Vienna, 3, 0)
s.add(vienna_days == 7)

# Santorini needs 4 days total
santorini_days = 0
# If Santorini is pre_lyon: days 1-6 (6 days)
santorini_days += If(pre_lyon == City.Santorini, 6, 0)
# If Santorini is post_ams: days 12-14 (3 days) + flight day 11
santorini_days += If(post_ams == City.Santorini, 3 + 1, 0)
s.add(santorini_days == 4)

# Ensure coverage of both Vienna and Santorini
s.add(Or(
    And(pre_lyon == City.Vienna, post_ams == City.Santorini),
    And(pre_lyon == City.Santorini, post_ams == City.Vienna)
))

if s.check() == sat:
    m = s.model()
    pre = m.evaluate(pre_lyon)
    post = m.evaluate(post_ams)
    
    print("Valid itinerary:")
    print(f"Days 1-6: {pre} (inclusive)")
    print(f"Days 7-9: Lyon (with flight from {pre} on day 7)")
    print(f"Days 9-11: Amsterdam (with flight from Lyon on day 9)")
    print(f"Days 12-14: {post} (with flight from Amsterdam on day 11)")
else:
    print("No valid itinerary found")