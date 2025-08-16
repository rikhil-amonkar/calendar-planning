# Solve the logic puzzle with Z3 and output the solution as the required JSON.

from z3 import Solver, Int, And, Or, Distinct, Implies
import json

# Indices 0..4 correspond to houses 1..5 (left to right)
N = 5
HOUSES = range(N)

# Enumerations (must match problem statement exactly)
Names = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
Foods = ["stir fry", "spaghetti", "stew", "grilled cheese", "pizza"]
CarModels = ["ford f150", "tesla model 3", "bmw 3 series", "toyota camry", "honda civic"]
PhoneModels = ["iphone 13", "google pixel 6", "samsung galaxy s21", "oneplus 9", "huawei p50"]
Occupations = ["teacher", "lawyer", "doctor", "artist", "engineer"]
Drinks = ["tea", "milk", "water", "root beer", "coffee"]

# Helper: get index of a value in its domain
def idx(domain, value):
    return domain.index(value)

# Variables: for each house, an Int representing the index in the corresponding domain
name = [Int(f"name_{i}") for i in HOUSES]
food = [Int(f"food_{i}") for i in HOUSES]
car = [Int(f"car_{i}") for i in HOUSES]
phone = [Int(f"phone_{i}") for i in HOUSES]
occ = [Int(f"occ_{i}") for i in HOUSES]
drink = [Int(f"drink_{i}") for i in HOUSES]

s = Solver()

# Domain constraints
for i in HOUSES:
    s.add(And(name[i] >= 0, name[i] < N))
    s.add(And(food[i] >= 0, food[i] < N))
    s.add(And(car[i] >= 0, car[i] < N))
    s.add(And(phone[i] >= 0, phone[i] < N))
    s.add(And(occ[i] >= 0, occ[i] < N))
    s.add(And(drink[i] >= 0, drink[i] < N))

# Each attribute is a permutation across houses
s.add(Distinct(name))
s.add(Distinct(food))
s.add(Distinct(car))
s.add(Distinct(phone))
s.add(Distinct(occ))
s.add(Distinct(drink))

# Indices for constants we use often
i_Eric = idx(Names, "Eric")
i_Peter = idx(Names, "Peter")
i_Arnold = idx(Names, "Arnold")
i_Alice = idx(Names, "Alice")

i_stirfry = idx(Foods, "stir fry")
i_spaghetti = idx(Foods, "spaghetti")
i_stew = idx(Foods, "stew")
i_grilled = idx(Foods, "grilled cheese")
i_pizza = idx(Foods, "pizza")

i_ford = idx(CarModels, "ford f150")
i_tesla = idx(CarModels, "tesla model 3")
i_bmw = idx(CarModels, "bmw 3 series")
i_camry = idx(CarModels, "toyota camry")
i_civic = idx(CarModels, "honda civic")

i_iphone = idx(PhoneModels, "iphone 13")
i_pixel = idx(PhoneModels, "google pixel 6")
i_samsung = idx(PhoneModels, "samsung galaxy s21")
i_oneplus = idx(PhoneModels, "oneplus 9")
i_huawei = idx(PhoneModels, "huawei p50")

i_teacher = idx(Occupations, "teacher")
i_lawyer = idx(Occupations, "lawyer")
i_doctor = idx(Occupations, "doctor")
i_artist = idx(Occupations, "artist")
i_engineer = idx(Occupations, "engineer")

i_tea = idx(Drinks, "tea")
i_milk = idx(Drinks, "milk")
i_water = idx(Drinks, "water")
i_rootbeer = idx(Drinks, "root beer")
i_coffee = idx(Drinks, "coffee")

# Clues:

# 1. The root beer lover is the person who owns a Honda Civic.
for i in HOUSES:
    s.add(Implies(drink[i] == i_rootbeer, car[i] == i_civic))
    s.add(Implies(car[i] == i_civic, drink[i] == i_rootbeer))

# 2. Milk is directly left of grilled cheese.
s.add(Or(*[And(drink[i] == i_milk, food[i+1] == i_grilled) for i in range(N-1)]))

# 3. Alice uses a Samsung Galaxy S21.
for i in HOUSES:
    s.add(Implies(name[i] == i_Alice, phone[i] == i_samsung))

# 4. Alice loves stir fry.
for i in HOUSES:
    s.add(Implies(name[i] == i_Alice, food[i] == i_stirfry))

# 5. The tea drinker is not in the fifth house.
s.add(drink[N-1] != i_tea)

# 6. The BMW 3 Series owner is somewhere to the left of the tea drinker.
s.add(Or(*[And(car[i] == i_bmw, drink[j] == i_tea) for i in HOUSES for j in HOUSES if i < j]))

# 7. The person who is a doctor is Arnold.
for i in HOUSES:
    s.add(Implies(name[i] == i_Arnold, occ[i] == i_doctor))
    s.add(Implies(occ[i] == i_doctor, name[i] == i_Arnold))

# 8. The iPhone 13 user is the coffee drinker.
for i in HOUSES:
    s.add(Implies(phone[i] == i_iphone, drink[i] == i_coffee))
    s.add(Implies(drink[i] == i_coffee, phone[i] == i_iphone))

# 9. The engineer owns a BMW 3 Series.
for i in HOUSES:
    s.add(Implies(occ[i] == i_engineer, car[i] == i_bmw))
    s.add(Implies(car[i] == i_bmw, occ[i] == i_engineer))

# 10. The stew lover uses an iPhone 13.
for i in HOUSES:
    s.add(Implies(food[i] == i_stew, phone[i] == i_iphone))
    s.add(Implies(phone[i] == i_iphone, food[i] == i_stew))

# 11. The doctor is directly left of the OnePlus 9 user.
s.add(Or(*[And(occ[i] == i_doctor, phone[i+1] == i_oneplus) for i in range(N-1)]))

# 12. The Honda Civic owner is directly left of the spaghetti eater.
s.add(Or(*[And(car[i] == i_civic, food[i+1] == i_spaghetti) for i in range(N-1)]))

# 13. The Google Pixel 6 user is the tea drinker.
for i in HOUSES:
    s.add(Implies(phone[i] == i_pixel, drink[i] == i_tea))
    s.add(Implies(drink[i] == i_tea, phone[i] == i_pixel))

# 14. Alice is an artist.
for i in HOUSES:
    s.add(Implies(name[i] == i_Alice, occ[i] == i_artist))

# 15. There is one house between Alice and the Ford F-150 owner.
s.add(Or(
    *[And(name[i] == i_Alice, car[i+2] == i_ford) for i in range(N-2)],
    *[And(name[i] == i_Alice, car[i-2] == i_ford) for i in range(2, N)]
))

# 16. Arnold owns a Toyota Camry.
for i in HOUSES:
    s.add(Implies(name[i] == i_Arnold, car[i] == i_camry))

# 17. Eric is in the fourth house (index 3).
s.add(name[3] == i_Eric)

# 18. The OnePlus 9 user is a lawyer.
for i in HOUSES:
    s.add(Implies(phone[i] == i_oneplus, occ[i] == i_lawyer))
    s.add(Implies(occ[i] == i_lawyer, phone[i] == i_oneplus))

# 19. The grilled cheese lover is Peter.
for i in HOUSES:
    s.add(Implies(name[i] == i_Peter, food[i] == i_grilled))

# Solve
if s.check() != 1:  # 1 == sat
    raise RuntimeError("No solution found")

m = s.model()

# Build JSON output
rows = []
for i in HOUSES:
    rows.append([
        str(i+1),
        Names[m[name[i]].as_long()],
        Foods[m[food[i]].as_long()],
        CarModels[m[car[i]].as_long()],
        PhoneModels[m[phone[i]].as_long()],
        Occupations[m[occ[i]].as_long()],
        Drinks[m[drink[i]].as_long()],
    ])

result = {
    "solution": {
        "header": ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"],
        "rows": rows
    }
}

print(json.dumps(result, ensure_ascii=False, indent=2))