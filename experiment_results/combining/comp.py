import csv




typ0 = ['F(?1)', 'G(?1)', 'G(!(?1))', '->(?1,U(!(p),q))', '->(?1,U(p,q))', 'G(->(q,?1))', 'G(->(q,?1))', '|(?1,F(&(p,F(q))))', 'G(&(p,->(!(q),U(!(q),?1))))']
typ1 = ['?u1(p)', '?u1(p)', '?u1(!(p))', '?b1(F(q),?b2(!(p),q))', '?b1(F(q),?b2(p,q))', '?u1(->(q,?u1(!(p))))', '?u1(->(q,?u1(p)))', '?b1(G(!(p)),F(?b2(p,F(q))))', 'G(&(p,?b1(!(q),?b2(!(q),&(r,!(q))))))'] 


typ0dict = {}
typ1dict = {}
	
with open('naive-sat.csv', 'r') as f:
	naive_reader = csv.DictReader(f)
	for row in naive_reader:
		
		row = dict(row)
		file, sketch = row['File'], row['Sketch'] 

		if sketch in typ0:

			if (file,sketch) in typ0dict:
				typ0dict[(file,sketch)].update(row)
			else:
				typ0dict[(file,sketch)] = row

		if sketch in typ1:

			if (file,sketch) in typ1dict:
				typ1dict[(file,sketch)].update(row)
			else:
				typ1dict[(file,sketch)] = row


with open('tree.csv', 'r') as f:
	tree_reader = csv.DictReader(f)


	for row in tree_reader:
		row = dict(row)
		file, sketch = row['File'], row['Sketch'] 
		if sketch in typ0:

			if (file,sketch) in typ0dict:
				typ0dict[(file,sketch)].update(row)
			else:
				typ0dict[(file,sketch)] = row

		if sketch in typ1:

			if (file,sketch) in typ1dict:
				typ1dict[(file,sketch)].update(row)
			else:
				typ1dict[(file,sketch)] = row


with open('tree-bmc.csv', 'r') as f:
	tree_bmc_reader = csv.DictReader(f)
	for row in tree_bmc_reader:
		row = dict(row)
		file, sketch = row['File'], row['Sketch'] 
		if sketch in typ0:

			if (file,sketch) in typ0dict:
				typ0dict[(file,sketch)].update(row)
			else:
				typ0dict[(file,sketch)] = row

		if sketch in typ1:

			if (file,sketch) in typ1dict:
				typ1dict[(file,sketch)].update(row)
			else:
				typ1dict[(file,sketch)] = row


with open('tree-suf.csv', 'r') as f:
	tree_suf_reader = csv.DictReader(f)
	for row in tree_suf_reader:
		row = dict(row)
		file, sketch = row['File'], row['Sketch'] 
		if sketch in typ0:

			if (file,sketch) in typ0dict:
				typ0dict[(file,sketch)].update(row)
			else:
				typ0dict[(file,sketch)] = row

		if sketch in typ1:

			if (file,sketch) in typ1dict:
				typ1dict[(file,sketch)].update(row)
			else:
				typ1dict[(file,sketch)] = row


with open('tree-suf-bmc.csv', 'r') as f:
	tree_suf_bmc_reader = csv.DictReader(f)
	for row in tree_suf_bmc_reader:
		row = dict(row)
		file, sketch = row['File'], row['Sketch'] 
		if sketch in typ0:

			if (file,sketch) in typ0dict:
				typ0dict[(file,sketch)].update(row)
			else:
				typ0dict[(file,sketch)] = row

		if sketch in typ1:

			if (file,sketch) in typ1dict:
				typ1dict[(file,sketch)].update(row)
			else:
				typ1dict[(file,sketch)] = row


with open('typ0-time.csv', 'w') as typ0file:
	fieldnames = typ0dict[list(typ0dict.keys())[0]].keys()
	writer = csv.DictWriter(typ0file, fieldnames=fieldnames)
	writer.writeheader()
	for k in typ0dict:
		writer.writerow(typ0dict[k])

with open('typ1-time.csv', 'w') as typ1file:
	fieldnames = typ1dict[list(typ1dict.keys())[0]].keys()
	writer = csv.DictWriter(typ1file, fieldnames=fieldnames)
	writer.writeheader()
	for k in typ1dict:
		writer.writerow(typ1dict[k])