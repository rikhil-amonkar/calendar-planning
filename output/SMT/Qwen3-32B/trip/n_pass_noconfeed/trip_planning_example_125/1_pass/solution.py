from z3 import *
import json

def main():
    # Define cities as an EnumSort
    Cities, (Stuttgart, Manchester, Seville) = EnumSort('Cities', ['Stuttgart', 'Manchester', 'Seville'])
    c0, c1, c2 = Consts('c0 c1 c2', Cities)
    s = Solver()

    # All cities are distinct
    s.add(Distinct(c0, c1, c2))

    # Durations for each city
    dur0 = If(c0 == Stuttgart, 6, If(c0 == Manchester, 4, 7))
    dur1 = If(c1 == Stuttgart, 6, If(c1 == Manchester, 4, 7))
    dur2 = If(c2 == Stuttgart, 6, If(c2 == Manchester, 4, 7))

    # Start days
    s0 = 1
    s1 = s0 + dur0 - 1
    s2 = s1 + dur1 - 1

    # End day of the last segment must be 15
    end_day = s2 + dur2 - 1
    s.add(end_day == 15)

    # Allowed transitions between consecutive cities
    allowed_transitions = [
        (Stuttgart, Manchester),
        (Manchester, Stuttgart),
        (Manchester, Seville),
        (Seville, Manchester)
    ]

    # Transition between c0 and c1
    trans01 = Or([And(c0 == ct[0], c1 == ct[1]) for ct in allowed_transitions])
    s.add(trans01)

    # Transition between c1 and c2
    trans12 = Or([And(c1 == ct[0], c2 == ct[1]) for ct in allowed_transitions])
    s.add(trans12)

    # Friend meeting constraint: Stuttgart's start day must be <=6
    s.add(Implies(c0 == Stuttgart, s0 <= 6))
    s.add(Implies(c1 == Stuttgart, s1 <= 6))
    s.add(Implies(c2 == Stuttgart, s2 <= 6))

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        # Extract the cities in order
        cities_order = [model[c0], model[c1], model[c2]]
        # Compute the start and end days for each city
        start_days = [s0]
        end_days = [s0 + model.evaluate(dur0).as_long() - 1]
        start_days.append(model.evaluate(s1).as_long())
        end_days.append(model.evaluate(s1).as_long() + model.evaluate(dur1).as_long() - 1)
        start_days.append(model.evaluate(s2).as_long())
        end_days.append(model.evaluate(s2).as_long() + model.evaluate(dur2).as_long() - 1)

        # Build the itinerary
        itinerary = []
        for i in range(3):
            city = cities_order[i].decl().name()
            start = start_days[i]
            end = end_days[i]
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})

        # Output as JSON
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()