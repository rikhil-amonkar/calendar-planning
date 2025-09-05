import json
from z3 import Int, Solver, Distinct, And

# Define the domain
houses = [0, 1, 2]  # 0-based indexing for houses 1..3

# Attributes
Names = ["Arnold", "Eric", "Peter"]
MusicGenres = ["pop", "rock", "classical"]
Children = ["Fred", "Meredith", "Bella"]
BookGenres = ["mystery", "romance", "science fiction"]

# Create position variables for each attribute value (position is house index 0..2)
def create_pos_vars(prefix, items):
    return {item: Int(f"{prefix}_{item.replace(' ', '_')}") for item in items}

pos_name = create_pos_vars("pos_name", Names)
pos_music = create_pos_vars("pos_music", MusicGenres)
pos_child = create_pos_vars("pos_child", Children)
pos_book = create_pos_vars("pos_book", BookGenres)

s = Solver()

# Domain constraints: each position is in 0..2
for d in [pos_name, pos_music, pos_child, pos_book]:
    for v in d.values():
        s.add(And(v >= 0, v < 3))

# Uniqueness within each category
s.add(Distinct(*pos_name.values()))
s.add(Distinct(*pos_music.values()))
s.add(Distinct(*pos_child.values()))
s.add(Distinct(*pos_book.values()))

# Clues:
# 1. The person's child is named Fred is directly left of the person who loves mystery books.
s.add(pos_child["Fred"] + 1 == pos_book["mystery"])

# 2. Peter is in the first house.
s.add(pos_name["Peter"] == 0)

# 3. The person who loves mystery books is the person who loves classical music.
s.add(pos_book["mystery"] == pos_music["classical"])

# 4. The person who loves science fiction books is the person's child is named Meredith.
s.add(pos_book["science fiction"] == pos_child["Meredith"])

# 5. Eric is the person who loves mystery books.
s.add(pos_name["Eric"] == pos_book["mystery"])

# 6. The person who loves rock music is somewhere to the right of the person who loves romance books.
s.add(pos_music["rock"] > pos_book["romance"])

assert s.check().r == 1  # sat

m = s.model()

# Invert position mappings to get attribute at each house index
def invert(pos_map, items):
    arr = [""] * 3
    for item in items:
        idx = m.evaluate(pos_map[item]).as_long()
        arr[idx] = item
    return arr

name_at = invert(pos_name, Names)
music_at = invert(pos_music, MusicGenres)
child_at = invert(pos_child, Children)
book_at = invert(pos_book, BookGenres)

# Prepare JSON output
rows = []
for i in range(3):
    row = [str(i + 1), name_at[i], music_at[i], child_at[i], book_at[i]]
    rows.append(row)

output = {
    "solution": {
        "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
        "rows": rows
    }
}

print(json.dumps(output))