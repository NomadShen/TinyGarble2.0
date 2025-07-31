#include <emp-tool/emp-tool.h>
#include <boost/program_options.hpp>
#include <boost/format.hpp>
#include "tinygarble/program_interface.h"
#include "tinygarble/program_interface_sh.h"
#include "tinygarble/TinyGarble_config.h"
#include <sys/resource.h>

using namespace std;
namespace po = boost::program_options;

void negotiation(auto TGPI){	

	
	struct rusage usage;
	double memory_usage;

	//bit_ width
	uint64_t bit_width       = 16; //bit width for reservation value
	uint64_t bit_width_rand  = 32; //bit width for random numbers

	uint64_t bit_width2      = bit_width + bit_width_rand - 1;
	uint64_t bit_width3      = bit_width2 + bit_width - 1;
	uint64_t bit_width4      = bit_width + bit_width - 1;

	// parameters
	uint64_t p = 1, c = 1, c_inv = 1; //pre-computed parameters for probabilities

    int64_t rv_a = 0, rv_b = 0;
	int64_t a_rand_0 = 0, b_rand_0 = 0;
	int64_t a_rand_1 = 0, b_rand_1 = 0;

	
	// Input reservation values for ALICE and BOB
	cout << "Input reservation value: ";
    if (TGPI->party == ALICE){
        cin >> rv_a;
        cout << "Garbler's reservation value: $" << rv_a << endl;
    }
    else{
        cin >> rv_b;
        cout << "Evaluator's reservation value: $" << rv_b << endl;
    }

	// Input randomness for ALICE and BOB
	cout << "Input Randomness 0: ";
    if (TGPI->party == ALICE){
        cin >> a_rand_0;
		cout << "Input Randomness 1: ";
        cin >> a_rand_1;
    }
    else{
        cin >> b_rand_0;
		cout << "Input Randomness 1: ";
        cin >> b_rand_1;
    }
    
	// Initialize the input labels for Alice and Bob
    auto rv_a_x = TGPI->TG_int_init(ALICE, bit_width, rv_a);
    auto rv_b_x = TGPI->TG_int_init(BOB  , bit_width, rv_b);

    auto a_rand_0_x = TGPI->TG_int_init(ALICE, bit_width_rand, a_rand_0 );
    auto b_rand_0_x = TGPI->TG_int_init(BOB  , bit_width_rand, b_rand_0 );
	
    auto a_rand_1_x = TGPI->TG_int_init(ALICE, bit_width_rand, a_rand_1 );
    auto b_rand_1_x = TGPI->TG_int_init(BOB  , bit_width_rand, b_rand_1 );
	



	// Generate input labels
    TGPI->gen_input_labels();

	// Retrieve input labels for both parties
    TGPI->retrieve_input_labels(rv_a_x, ALICE, bit_width);
    TGPI->retrieve_input_labels(rv_b_x, BOB, bit_width);
	
    TGPI->retrieve_input_labels(a_rand_0_x, ALICE, bit_width_rand);
    TGPI->retrieve_input_labels(b_rand_0_x, BOB  , bit_width_rand);
	
    TGPI->retrieve_input_labels(a_rand_1_x, ALICE, bit_width_rand);
    TGPI->retrieve_input_labels(b_rand_1_x, BOB  , bit_width_rand);

	
	Timer T;	
	uint64_t dc;
	double dt;
	T.start();

	auto rf_x = TGPI->TG_int(bit_width3);

	// Processing the random number
	auto r0_x = TGPI->TG_int(bit_width_rand);
	auto r1_x = TGPI->TG_int(bit_width_rand);

	TGPI->xor_(r0_x, a_rand_0_x, b_rand_0_x, bit_width_rand);
	
	TGPI->xor_(r1_x, a_rand_1_x, b_rand_1_x, bit_width_rand);

	auto p_x = TGPI->TG_int_init(PUBLIC, bit_width_rand, p);
	auto c_x = TGPI->TG_int_init(PUBLIC, bit_width_rand, c);

	auto f0_x = TGPI->TG_int(1);
	auto f1_x = TGPI->TG_int(1);

	TGPI->lt(f0_x, r0_x, p, bit_width_rand);
	TGPI->lt(f1_x, r1_x, c, bit_width_rand);

	// Act 1
	auto r2_t_x = TGPI->TG_int(bit_width2);
	// r2 = c*rv_a
	TGPI->mult(r2_t_x, rv_a_x, c, bit_width, bit_width_rand);
	auto r2_x = TGPI->TG_int(bit_width);
	TGPI->right_shift(r2_x, r2_t_x, bit_width_rand - 1, bit_width2);
	TGPI->ifelse(r2_x, f0_x, r2_x, rv_a_x, bit_width);

	// Act 2
	auto acc_a2_x = TGPI->TG_int(1);
	auto rej_a2_x = TGPI->TG_int(1);
	TGPI->lt(acc_a2_x, rv_b_x, r2_x, bit_width);

	auto r3_x = TGPI->TG_int(bit_width3);
	auto r2dc_x = TGPI->TG_int(bit_width3);
	auto r2dc_t_x = TGPI->TG_int(bit_width3);
	// r3 = max(r2/c, rv_b)
	TGPI->mult(r2dc_t_x, r2_x, c_inv, bit_width, bit_width_rand + bit_width - 1);
	TGPI->right_shift(r2dc_x, r2dc_t_x, bit_width_rand - 1, bit_width3);
	TGPI->max(r3_x, r2dc_x, rv_b_x, bit_width4, bit_width);

	auto r2_ext_x = TGPI->TG_int(bit_width4);
	TGPI->assign(r2_ext_x, r2_x, bit_width4, bit_width);
	TGPI->ifelse(rf_x, acc_a2_x, r2_ext_x, int64_t(0), bit_width4);
	TGPI->not_(rej_a2_x, acc_a2_x, 1);

	// Act 3
	auto acc_a3_x = TGPI->TG_int(1);
	auto rej_a3_x = TGPI->TG_int(1);
	TGPI->lt(acc_a3_x, r3_x, rv_a_x, bit_width4, bit_width);
	TGPI->and_(acc_a3_x, acc_a3_x, f1_x, 1);

	TGPI->not_(rej_a3_x, acc_a3_x, 1);

	TGPI->and_(acc_a3_x, acc_a3_x, rej_a2_x, 1);
	TGPI->and_(rej_a3_x, rej_a3_x, rej_a2_x, 1);

	TGPI->ifelse(rf_x, acc_a3_x, r3_x, rf_x, bit_width4);
	TGPI->ifelse(rf_x, rej_a3_x, int64_t(0), rf_x, bit_width4);

    int64_t rf = TGPI->reveal(rf_x, bit_width4, true);

	T.get(dc, dt);
	cout << "Evaluation Time:\t" << dc << "\tcc\t" << dt << "\tms" << endl;

	getrusage(RUSAGE_SELF, &usage);	
	memory_usage = (double)usage.ru_maxrss/1024;
	cout << "Memory Usage: " << memory_usage << " MB" << endl;

	cout << "Final Ransom:\t" << rf << endl;


	// release memory
	TGPI->clear_TG_int(rv_a_x);
	TGPI->clear_TG_int(rv_b_x);

	TGPI->clear_TG_int(a_rand_0_x);
	TGPI->clear_TG_int(b_rand_0_x);
	TGPI->clear_TG_int(a_rand_1_x);
	TGPI->clear_TG_int(b_rand_1_x);
	
	TGPI->clear_TG_int(p_x);
	TGPI->clear_TG_int(c_x);
	
	TGPI->clear_TG_int(r0_x);
	TGPI->clear_TG_int(r1_x);
	
	TGPI->clear_TG_int(f0_x);
	TGPI->clear_TG_int(f1_x);

	TGPI->clear_TG_int(acc_a2_x);
	TGPI->clear_TG_int(rej_a2_x);

	TGPI->clear_TG_int(acc_a3_x);
	TGPI->clear_TG_int(rej_a3_x);
	
	delete TGPI;
}

int main(int argc, char** argv) {
	int party = 1, port = 1234;
	string netlist_address;
	string server_ip;
	
	po::options_description desc{"Negotiation \nAllowed options"};
	desc.add_options()  //
	("help,h", "produce help message")  //
	("party,k", po::value<int>(&party)->default_value(1), "party id: 1 for garbler, 2 for evaluator")  //
	("port,p", po::value<int>(&port)->default_value(1234), "socket port")  //
	("server_ip,s", po::value<string>(&server_ip)->default_value("127.0.0.1"), "server's IP.")
	("sh", "semi-honest setting (default is malicious)");
	
	po::variables_map vm;
	try {
		po::parsed_options parsed = po::command_line_parser(argc, argv).options(desc).allow_unregistered().run();
		po::store(parsed, vm);
		if (vm.count("help")) {
			cout << desc << endl;
			return 0;
		}
		po::notify(vm);
	}catch (po::error& e) {
		cout << "ERROR: " << e.what() << endl << endl;
		cout << desc << endl;
		return -1;
	}
		
	NetIO* io = new NetIO(party==ALICE ? nullptr:server_ip.c_str(), port, true);
	io->set_nodelay();
	
	TinyGarblePI_SH* TGPI_SH;
	TinyGarblePI* TGPI; 
	
	if (vm.count("sh")){
		cout << "testing program interface in semi-honest setting" << endl;
		TGPI_SH = new TinyGarblePI_SH(io, party);
		io->flush();
		negotiation(TGPI_SH);		
	}
	else {
		cout << "Negotiation in malicious setting" << endl;
		TGPI = new TinyGarblePI(io, party, 192, 64);
		io->flush();
		negotiation(TGPI);
	}
	
	delete io;
	
	return 0;
}
