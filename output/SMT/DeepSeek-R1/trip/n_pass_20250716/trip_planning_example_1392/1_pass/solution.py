from z3 import *

# Define the City datatype
City = Datatype('City')
City.declare('Naples')
City.declare('Valencia')
City.declare('Stuttgart')
City.declare('Split')
City.declare('Venice')
City.declare('Amsterdam')
City.declare('Nice')
City.declare('Barcelona')
City.declare('Porto')
City = City.create()

# City constants
Naples = City.Naples
Valencia = City.Valencia
Stuttgart = City.Stuttgart
Split = City.Split
Venice = City.Venice
Amsterdam = City.Amsterdam
Nice = City.Nice
Barcelona = City.Barcelona
Porto = City.Porto

# Duration lookup
duration_dict = {
    Naples: 3,
    Valencia: 5,
    Stuttgart: 2,
    Split: 5,
    Venice: 5,
    Amsterdam: 4,
    Nice: 2,
    Barcelona: 2,
    Porto: 4
}

# Direct flight edges (undirected, so include both (a,b) and (b,a))
edges = [
    (Venice, Nice),
    (Naples, Amsterdam),
    (Barcelona, Nice),
    (Amsterdam, Nice),
    (Stuttgart, Valencia),
    (Stuttgart, Porto),
    (Split, Stuttgart),
    (Split, Naples),
    (Valencia, Amsterdam),
    (Barcelona, Porto),
    (Valencia, Naples),
    (Venice, Amsterdam),
    (Barcelona, Naples),
    (Barcelona, Valencia),
    (Split, Amsterdam),
    (Barcelona, Venice),
    (Stuttgart, Amsterdam),
    (Naples, Nice),
    (Venice, Stuttgart),
    (Split, Barcelona),
    (Porto, Nice),
    (Barcelona, Stuttgart),
    (Venice, Naples),
    (Porto, Amsterdam),
    (Porto, Valencia),
    (Stuttgart, Naples),
    (Barcelona, Amsterdam)
]

# Include both directions for edges
directed_edges = edges + [(b, a) for (a, b) in edges]

# Free cities: all except Barcelona, Venice, Nice
free_cities = [Naples, Valencia, Stuttgart, Split, Amsterdam, Porto]

# Create free position variables
P0 = Const('P0', City)
P3 = Const('P3', City)
P4 = Const('P4', City)
P5 = Const('P5', City)
P6 = Const('P6', City)
P7 = Const('P7', City)

# Build the entire sequence P
P = [
    P0,
    Barcelona,
    Venice,
    P3,
    P4,
    P5,
    P6,
    P7,
    Nice
]

solver = Solver()

# Constraint: P0 is either Valencia or Split
solver.add(Or(P0 == Valencia, P0 == Split))

# Constraint: all free positions are distinct and from free_cities
solver.add(Distinct([P0, P3, P4, P5, P6, P7]))
for var in [P0, P3, P4, P5, P6, P7]:
    solver.add(Or([var == c for c in free_cities]))

# Flight constraints between consecutive cities
for i in range(8):
    solver.add(Or([And(P[i] == a, P[i+1] == b) for (a, b) in directed_edges]))

# Define a duration function for Z3
dur = Function('dur', City, IntSort())
solver.add(dur(Naples) == 3)
solver.add(dur(Valencia) == 5)
solver.add(dur(Stuttgart) == 2)
solver.add(dur(Split) == 5)
solver.add(dur(Venice) == 5)
solver.add(dur(Amsterdam) == 4)
solver.add(dur(Nice) == 2)
solver.add(dur(Barcelona) == 2)
solver.add(dur(Porto) == 4)

# Cumulative sums for the first few positions
cum0 = dur(P[0])
cum1 = cum0 + dur(P[1])
cum2 = cum1 + dur(P[2])
cum3 = cum2 + dur(P[3])
cum4 = cum3 + dur(P[4])
cum5 = cum4 + dur(P[5])
cum6 = cum5 + dur(P[6])
cum7 = cum6 + dur(P[7])

# Naples constraint: must be in positions 3 to 7 and start day between 16 and 20
naples_in_pos = [P[i] == Naples for i in range(3, 8)]
solver.add(Or(naples_in_pos))  # Naples must be in one of these positions

# Define start days for each possible position of Naples
s_naples = Int('s_naples')
s_naples = If(P[3] == Naples, 1 + cum2 - 3, 
            If(P[4] == Naples, 1 + cum3 - 4,
            If(P[5] == Naples, 1 + cum4 - 5,
            If(P[6] == Naples, 1 + cum5 - 6,
            If(P[7] == Naples, 1 + cum6 - 7,
            0)))))
solver.add(s_naples >= 16, s_naples <= 20)

# Solve the model
if solver.check() == sat:
    model = solver.model()
    # Map Z3 constants to city names
    city_const_to_name = {
        Naples: "Naples",
        Valencia: "Valencia",
        Stuttgart: "Stuttgart",
        Split: "Split",
        Venice: "Venice",
        Amsterdam: "Amsterdam",
        Nice: "Nice",
        Barcelona: "Barcelona",
        Porto: "Porto"
    }
    # Get the actual sequence
    P_actual = []
    for i, city_var in enumerate(P):
        if i in [0, 3, 4, 5, 6, 7]:
            c = model[city_var]
            P_actual.append(city_const_to_name[c])
        else:
            P_actual.append(city_const_to_name[city_var])
    
    # Generate itinerary
    itinerary = []
    s = 1
    for idx, city in enumerate(P_actual):
        d = duration_dict[city_const_to_name.inverse[city]]
        end = s + d - 1
        itinerary.append({"day_range": f"Day {s}-{end}", "place": city})
        if idx < 8:
            itinerary.append({"day_range": f"Day {end}", "place": city})
            itinerary.append({"day_range": f"Day {end}", "place": P_actual[idx+1]})
            s = end
    # Output the result
    print({"itinerary": itinerary})
else:
    print("No solution found")